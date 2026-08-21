package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.ToNumberPolicy;
import com.google.gson.reflect.TypeToken;
import edu.uva.liftlab.graphchecker.annotation.CausynthFault;
import edu.uva.liftlab.graphchecker.causynth.CausynthJson;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
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
import java.util.Map;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.zip.GZIPInputStream;
import java.util.zip.GZIPOutputStream;

/**
 * Refines the cheap static candidate graph with one concrete REGION_STATE
 * execution.  Static discovery chooses methods; receiver/value object identity
 * supplies field paths.  No synthetic access-path cell is created.
 */
final class RuntimeRefinedGraphBuilder {
    static final int REFINEMENT_SCHEMA_VERSION = 1;
    static final String GRAPH_KIND = "RUNTIME_REFINED_DATAFLOW";
    static final String FIELD_ACCESS_AUTHORITY =
            "EXACT_RUNTIME_ACTIVATION_FIELD_ACCESS_V1";
    static final String ASSOCIATIVE_MEMBER_AUTHORITY =
            "EXACT_RUNTIME_ASSOCIATIVE_PUT_PROVENANCE_V1";

    private static final Type ROW_TYPE =
            new TypeToken<Map<String, Object>>() { }.getType();
    private static final Gson GSON = new GsonBuilder()
            .setObjectToNumberStrategy(ToNumberPolicy.LONG_OR_DOUBLE)
            .create();

    private RuntimeRefinedGraphBuilder() {
    }

    static Result refine(File candidateGraph, File selectedSkeletons,
                         Collection<Map<String, Object>> runtimeInstances,
                         List<RuntimeRegionPlanner.MethodEvent> methods,
                         List<RuntimeRegionPlanner.RuntimeEvent> runtime,
                         List<RuntimeRegionPlanner.FieldAccessEvent> fields,
                         List<RuntimeRegionPlanner.ProtocolEvent> protocol,
                         Path output) throws IOException {
        return refine(candidateGraph, selectedSkeletons, runtimeInstances,
                methods, runtime, fields,
                Collections.<RuntimeRegionPlanner.ArrayAccessEvent>emptyList(),
                protocol, Collections.<Map<String, Object>>emptyList(),
                output);
    }

    static Result refine(File candidateGraph, File selectedSkeletons,
                         Collection<Map<String, Object>> runtimeInstances,
                         List<RuntimeRegionPlanner.MethodEvent> methods,
                         List<RuntimeRegionPlanner.RuntimeEvent> runtime,
                         List<RuntimeRegionPlanner.FieldAccessEvent> fields,
                         List<RuntimeRegionPlanner.ArrayAccessEvent> arrays,
                         List<RuntimeRegionPlanner.ProtocolEvent> protocol,
                         Path output) throws IOException {
        return refine(candidateGraph, selectedSkeletons, runtimeInstances,
                methods, runtime, fields, arrays, protocol,
                Collections.<Map<String, Object>>emptyList(), output);
    }

    static Result refine(File candidateGraph, File selectedSkeletons,
                         Collection<Map<String, Object>> runtimeInstances,
                         List<RuntimeRegionPlanner.MethodEvent> methods,
                         List<RuntimeRegionPlanner.RuntimeEvent> runtime,
                         List<RuntimeRegionPlanner.FieldAccessEvent> fields,
                         List<RuntimeRegionPlanner.ArrayAccessEvent> arrays,
                         List<RuntimeRegionPlanner.ProtocolEvent> protocol,
                         Collection<Map<String, Object>> occurrenceLinks,
                         Path output) throws IOException {
        if (candidateGraph == null || !candidateGraph.isFile()) {
            throw new IOException("candidate static graph not found: "
                    + candidateGraph);
        }
        if (selectedSkeletons == null || !selectedSkeletons.isFile()) {
            throw new IOException("selected region skeletons not found: "
                    + selectedSkeletons);
        }

        SkeletonCatalog skeletons = SkeletonCatalog.read(selectedSkeletons);
        Set<String> selectedMethods = skeletons.methods;
        List<RuntimeRegionPlanner.MethodEvent> methodEvents = sortedMethods(
                methods);
        List<RuntimeRegionPlanner.RuntimeEvent> runtimeEvents = sortedRuntime(
                runtime);
        List<RuntimeRegionPlanner.FieldAccessEvent> fieldEvents = sortedFields(
                fields);
        Map<String, List<RuntimeRegionPlanner.ArrayAccessEvent>>
                arraysByObject = arraysByObject(arrays, methodEvents);
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
                    int unitIndex = unitIndex(event.siteId);
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
                                            container, event, completion,
                                            callArguments.getOrDefault(
                                                    event.invocationId,
                                                    Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList()),
                                            activationFields));
                        }
                    }
                }
        }

        final List<Map<String, Object>> refined = new ArrayList<>();
        final int[] runtimeBoundCounter = {0};
        // The candidate graph can be multi-gigabyte.  Parse it in parallel
        // batches and process rows strictly in file order, so the refined
        // output is identical to a sequential pass while the full candidate
        // row set never has to be resident at once.
        streamRows(candidateGraph, candidate -> {
            requireCandidateEdge(candidate, candidateGraph);
            String method = string(candidate.get("method"));
            String candidateTransfer = string(candidate.get(
                    "transferKind"));
            if (!selectedMethods.contains(method)) {
                return;
            }
            Map<String, Object> edge = new LinkedHashMap<>(candidate);
            edge.put("refinementSchemaVersion", REFINEMENT_SCHEMA_VERSION);
            edge.put("graphKind", GRAPH_KIND);

            String transfer = string(edge.get("transferKind"));
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
                    runtimeBoundCounter[0]++;
                }
            } else if ("accessor_field_return".equals(
                    string(edge.get("kind")))) {
                List<RuntimeAccessorBinding> bindings = values(
                        accessorBindingsBySite.get(AccessorSite.from(edge)));
                if (bindings.isEmpty()) {
                    edge.put("runtimeObserved", false);
                } else {
                    edge.put("runtimeAccessorBindings",
                            encodeAccessorBindings(bindings, edge,
                                    arraysByObject));
                    edge.put("runtimeObserved", true);
                    runtimeBoundCounter[0]++;
                }
            } else if ("HEAP_READ".equals(transfer)
                    || "HEAP_WRITE".equals(transfer)) {
                StaticSite site = StaticSite.from(edge);
                List<RuntimeFieldBinding> bindings = values(
                        bindingsBySite.get(site));
                if (!bindings.isEmpty()) {
                    List<Map<String, Object>> encoded = encodeBindings(
                            bindings, arraysByObject);
                    edge.put("runtimeFieldBindings", encoded);
                    List<String> uniquePath = uniquePath(bindings);
                    List<String> uniqueDeclarations =
                            uniqueDeclarations(bindings);
                    if (!uniquePath.isEmpty()) {
                        edge.put("fieldPath", uniquePath);
                        edge.put("fieldPathDeclarations", uniqueDeclarations);
                    }
                    edge.put("runtimeObserved", true);
                    runtimeBoundCounter[0]++;
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
        return new Result(output, refined, runtimeBoundCounter[0],
                activations.size(), selectedMethods.size());
    }

    /** Receives rows strictly in file order. */
    private interface RowSink {
        void accept(Map<String, Object> row) throws IOException;
    }

    /**
     * Streams JSONL rows in file order while parsing batches on background
     * threads.  Row acceptance is unchanged: every non-blank line must be a
     * JSON object, exactly as {@link #readRows(File)} required.
     */
    private static void streamRows(File file, RowSink sink)
            throws IOException {
        int threads = Math.max(1, Math.min(8,
                Runtime.getRuntime().availableProcessors() - 2));
        int configured = Integer.getInteger(
                "causynth.aggregate.threads", 0);
        if (configured > 0) {
            threads = Math.min(configured, 32);
        }
        final int workerCount = threads;
        ExecutorService executor = Executors.newFixedThreadPool(workerCount,
                runnable -> {
                    Thread thread = new Thread(runnable,
                            "causynth-candidate-parse");
                    thread.setDaemon(true);
                    return thread;
                });
        try (BufferedReader input = reader(file.toPath())) {
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

    /**
     * Rewrites integral boxed numbers to Long in place, which is exactly the
     * value domain produced by writing with {@link CausynthJson} and parsing
     * with the LONG_OR_DOUBLE strategy.
     */
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

    private static Object normalizeScalar(Object value) {
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
                    || CausynthFault.isBooleanMarkerSignature(
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
                    string(instance.get("kind")))) {
                throw new IOException("invalid runtime activation supplied "
                        + "to refinement");
            }
            String regionId = string(instance.get("regionId"));
            Skeleton skeleton = skeletons.byRegion.get(regionId);
            long rootCallId = longNumber(instance.get("rootCallId"), -1L);
            RuntimeRegionPlanner.MethodEvent root =
                    methodByCall.get(rootCallId);
            if (skeleton == null || root == null) {
                throw new IOException("runtime activation cannot be bound to "
                        + "selected skeleton: " + regionId + "#call"
                        + rootCallId);
            }
            Set<Long> calls = longNumbers(instance.get("callIds"));
            if (calls.isEmpty() || !calls.contains(rootCallId)) {
                throw new IOException("runtime activation has no rooted call "
                        + "subtree: " + regionId + "#call" + rootCallId);
            }
            result.add(new Activation(skeleton, root, calls));
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

    private static int unitIndex(String siteId) {
        int marker = siteId == null ? -1 : siteId.lastIndexOf("#u");
        if (marker < 0 || marker + 2 >= siteId.length()) return -1;
        try {
            return Integer.parseInt(siteId.substring(marker + 2));
        } catch (NumberFormatException ignored) {
            return -1;
        }
    }

    private static void addAllUnique(List<String> target,
                                     List<String> additions) {
        for (String addition : values(additions)) {
            if (!target.contains(addition)) {
                target.add(addition);
            }
        }
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
        return encodeBindings(bindings,
                Collections.<String, List<RuntimeRegionPlanner.ArrayAccessEvent>>
                        emptyMap());
    }

    private static List<Map<String, Object>> encodeBindings(
            Collection<RuntimeFieldBinding> bindings,
            Map<String, List<RuntimeRegionPlanner.ArrayAccessEvent>>
                    arraysByObject) {
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        for (RuntimeFieldBinding binding : bindings) {
            Map<String, Object> encoded = binding.toMap();
            attachArrayElementBindings(encoded, binding.root.sourceKey,
                    binding.event.valueObjectId, arraysByObject);
            unique.put(CausynthJson.write(encoded), encoded);
        }
        return new ArrayList<>(unique.values());
    }

    private static Map<String, List<RuntimeRegionPlanner.ArrayAccessEvent>>
            arraysByObject(
            Collection<RuntimeRegionPlanner.ArrayAccessEvent> events,
            Collection<RuntimeRegionPlanner.MethodEvent> methods) {
        Map<Long, String> sourceKeyByCall = new LinkedHashMap<>();
        for (RuntimeRegionPlanner.MethodEvent method : methods) {
            sourceKeyByCall.put(method.callId, method.sourceKey);
        }
        Map<String, List<RuntimeRegionPlanner.ArrayAccessEvent>> result =
                new LinkedHashMap<>();
        List<RuntimeRegionPlanner.ArrayAccessEvent> sorted =
                new ArrayList<>(events == null
                        ? Collections.<RuntimeRegionPlanner.ArrayAccessEvent>
                                emptyList() : events);
        sorted.sort((left, right) -> Long.compare(left.seq, right.seq));
        for (RuntimeRegionPlanner.ArrayAccessEvent event : sorted) {
            String sourceKey = sourceKeyByCall.get(event.callId);
            if (event.arrayObjectId == 0 || sourceKey == null
                    || sourceKey.isEmpty()) continue;
            result.computeIfAbsent(sourceKey + "\n" + event.arrayObjectId,
                    ignored -> new ArrayList<>()).add(event);
        }
        return result;
    }

    private static List<Map<String, Object>> encodeAccessorBindings(
            Collection<RuntimeAccessorBinding> bindings,
            Map<String, Object> edge,
            Map<String, List<RuntimeRegionPlanner.ArrayAccessEvent>>
                    arraysByObject) {
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        for (RuntimeAccessorBinding binding : bindings) {
            Map<String, Object> encoded = binding.toMap(edge);
            attachArrayElementBindings(encoded,
                    binding.activation.root.sourceKey,
                    binding.returned.objectId, arraysByObject);
            unique.put(CausynthJson.write(encoded), encoded);
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
            unique.put(CausynthJson.write(encoded), encoded);
        }
        return new ArrayList<>(unique.values());
    }

    /** Carries exact element identity with every reference-array value. */
    private static void attachArrayElementBindings(
            Map<String, Object> encoded, String sourceKey, int valueObjectId,
            Map<String, List<RuntimeRegionPlanner.ArrayAccessEvent>>
                    arraysByObject) {
        List<RuntimeRegionPlanner.ArrayAccessEvent> accesses =
                arraysByObject.getOrDefault(sourceKey + "\n" + valueObjectId,
                        Collections.<RuntimeRegionPlanner.ArrayAccessEvent>
                                emptyList());
        if (accesses.isEmpty()) return;
        List<Map<String, Object>> rows = new ArrayList<>();
        for (RuntimeRegionPlanner.ArrayAccessEvent access : accesses) {
            Map<String, Object> row = new LinkedHashMap<>();
            row.put("kind", access.kind);
            row.put("eventSeq", access.seq);
            row.put("method", access.method);
            row.put("callId", access.callId);
            row.put("siteId", access.siteId);
            row.put("unitIndex", access.unitIndex);
            row.put("arrayObjectId", access.arrayObjectId);
            row.put("arrayIndex", access.index);
            row.put("elementObjectId", access.elementObjectId);
            row.put("authority",
                    "EXACT_RUNTIME_REFERENCE_ARRAY_ELEMENT_V1");
            rows.add(row);
        }
        encoded.put("runtimeArrayElementBindings", rows);
    }

    private static List<String> uniquePath(
            Collection<RuntimeFieldBinding> bindings) {
        List<String> selected = null;
        for (RuntimeFieldBinding binding : bindings) {
            List<String> path = binding.path.fieldNames();
            if (selected == null) {
                selected = path;
            } else if (!selected.equals(path)) {
                return Collections.emptyList();
            }
        }
        return selected == null ? Collections.emptyList() : selected;
    }

    private static List<String> uniqueDeclarations(
            Collection<RuntimeFieldBinding> bindings) {
        List<String> selected = null;
        for (RuntimeFieldBinding binding : bindings) {
            List<String> path = binding.path.fieldDeclarations();
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

    private static List<Map<String, Object>> readRows(File file)
            throws IOException {
        List<Map<String, Object>> result = new ArrayList<>();
        try (BufferedReader reader = reader(file.toPath())) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) {
                    continue;
                }
                Map<String, Object> row = GSON.fromJson(line, ROW_TYPE);
                if (row == null) {
                    throw new IOException("null JSON row in " + file);
                }
                result.add(row);
            }
        }
        return result;
    }

    private static BufferedReader reader(Path path) throws IOException {
        InputStream input = Files.newInputStream(path);
        try {
            if (path.getFileName().toString().endsWith(".gz")) {
                input = new GZIPInputStream(input);
            }
            return new BufferedReader(new InputStreamReader(input,
                    StandardCharsets.UTF_8));
        } catch (IOException exception) {
            input.close();
            throw exception;
        }
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
                writer.write(CausynthJson.write(row));
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

    private static String associativeMemberToken(String sourceKey,
                                                  int containerObjectId,
                                                  long invocationId) {
        String provenance = sourceKey + "\n" + containerObjectId + "\n"
                + invocationId;
        return "MEMBER." + UUID.nameUUIDFromBytes(provenance.getBytes(
                StandardCharsets.UTF_8));
    }

    private static String string(Object value) {
        return value == null || "null".equals(String.valueOf(value))
                ? "" : String.valueOf(value);
    }

    private static int integer(Object value, int fallback) {
        if (value instanceof Number) {
            return ((Number) value).intValue();
        }
        try {
            return Integer.parseInt(string(value));
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long longNumber(Object value, long fallback) {
        return value instanceof Number ? ((Number) value).longValue()
                : fallback;
    }

    private static Set<Long> longNumbers(Object value) {
        Set<Long> result = new LinkedHashSet<>();
        if (value instanceof Collection<?>) {
            for (Object item : (Collection<?>) value) {
                if (item instanceof Number) {
                    result.add(((Number) item).longValue());
                }
            }
        }
        return result;
    }

    private static <T> List<T> values(List<T> values) {
        return values == null ? Collections.emptyList() : values;
    }

    static final class Result {
        final Path output;
        /** Refined rows, normalized to the exact JSONL round-trip domain. */
        final List<Map<String, Object>> rows;
        final int edgeCount;
        final int runtimeBoundEdgeCount;
        final int activationCount;
        final int selectedMethodCount;

        private Result(Path output, List<Map<String, Object>> rows,
                       int runtimeBoundEdgeCount,
                       int activationCount,
                       int selectedMethodCount) {
            this.output = output;
            this.rows = rows;
            this.edgeCount = rows.size();
            this.runtimeBoundEdgeCount = runtimeBoundEdgeCount;
            this.activationCount = activationCount;
            this.selectedMethodCount = selectedMethodCount;
        }
    }

    private static final class SkeletonCatalog {
        private final Set<String> methods = new LinkedHashSet<>();
        private final Set<String> roots = new LinkedHashSet<>();
        private final List<Skeleton> skeletons = new ArrayList<>();
        private final Map<String, Skeleton> byRegion = new LinkedHashMap<>();
        private final Map<String, List<String>> regionsByMethod =
                new LinkedHashMap<>();

        private static SkeletonCatalog read(File file) throws IOException {
            SkeletonCatalog result = new SkeletonCatalog();
            for (Map<String, Object> row : readRows(file)) {
                if (integer(row.get("schemaVersion"), -1) != 3
                        || !"REGION_SKELETON".equals(
                        string(row.get("kind")))) {
                    throw new IOException("invalid selected skeleton row in "
                            + file);
                }
                String region = string(row.get("regionId"));
                String root = string(row.get("rootMethod"));
                if (region.isEmpty() || root.isEmpty()) {
                    throw new IOException("selected skeleton requires regionId"
                            + " and rootMethod: " + file);
                }
                result.roots.add(root);
                Object methods = row.get("methods");
                if (!(methods instanceof Collection<?>)) {
                    throw new IOException("selected skeleton requires methods: "
                            + file);
                }
                Set<String> skeletonMethods = new LinkedHashSet<>();
                for (Object value : (Collection<?>) methods) {
                    String method = string(value);
                    if (method.isEmpty()) {
                        continue;
                    }
                    result.methods.add(method);
                    skeletonMethods.add(method);
                    result.regionsByMethod.computeIfAbsent(method,
                            ignored -> new ArrayList<>()).add(region);
                }
                Set<String> anchors = new LinkedHashSet<>();
                Object anchorMethods = row.get("anchorMethods");
                if (anchorMethods instanceof Collection<?>) {
                    for (Object value : (Collection<?>) anchorMethods) {
                        String anchor = string(value);
                        if (!anchor.isEmpty()) anchors.add(anchor);
                    }
                }
                if (anchors.isEmpty()) {
                    String anchor = string(row.get("anchorMethod"));
                    if (!anchor.isEmpty()) anchors.add(anchor);
                }
                Skeleton skeleton = new Skeleton(region, root,
                        anchors, skeletonMethods);
                result.skeletons.add(skeleton);
                result.byRegion.put(region, skeleton);
            }
            if (result.methods.isEmpty()) {
                throw new IOException("selected skeletons contain no methods: "
                        + file);
            }
            return result;
        }
    }

    private static final class Skeleton {
        private final String regionId;
        private final String rootMethod;
        private final Set<String> anchorMethods;
        private final Set<String> methods;

        private Skeleton(String regionId, String rootMethod,
                         Set<String> anchorMethods, Set<String> methods) {
            this.regionId = regionId;
            this.rootMethod = rootMethod;
            this.anchorMethods = anchorMethods;
            this.methods = methods;
        }
    }

    private static final class Activation {
        private final String regionId;
        private final RuntimeRegionPlanner.MethodEvent root;
        private final Set<Long> calls;
        private Activation(Skeleton skeleton,
                           RuntimeRegionPlanner.MethodEvent root,
                           Set<Long> calls) {
            this.regionId = skeleton.regionId;
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
            this.method = string(method);
            this.unitIndex = unitIndex;
            this.operation = string(operation);
            this.field = string(field);
        }

        private static StaticSite from(Map<String, Object> edge) {
            String transfer = string(edge.get("transferKind"));
            boolean read = "HEAP_READ".equals(transfer);
            return new StaticSite(string(edge.get("method")),
                    integer(edge.get("unitIndex"), -1),
                    read ? "FIELD_READ" : "FIELD_WRITE",
                    read ? string(edge.get("fromCell"))
                            : string(edge.get("toCell")));
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
            this.method = string(method);
            this.siteId = string(siteId);
            this.declaredCallee = string(declaredCallee);
        }

        private static AccessorSite from(Map<String, Object> edge) {
            return new AccessorSite(string(edge.get("method")),
                    string(edge.get("siteId")),
                    string(edge.get("invoke")));
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
            result.put("unitIndex", unitIndex(enter.siteId));
            result.put("siteId", enter.siteId);
            result.put("eventSeq", returned.seq);
            result.put("receiverObjectId", enter.objectId);
            result.put("receiverRuntimeType", enter.runtimeType);
            result.put("primitiveValue", returned.primitiveValue);
            if (returned.objectId != 0) {
                result.put("valueObjectId", returned.objectId);
                result.put("valueRuntimeType", returned.runtimeType);
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
        private final List<RuntimeRegionPlanner.RuntimeEvent>
                mutationArguments;
        private final List<RuntimeRegionPlanner.FieldAccessEvent>
                activationFields;

        private RuntimeFieldBinding(String regionId,
                                    RuntimeRegionPlanner.MethodEvent root,
                                    RuntimeRegionPlanner.FieldAccessEvent event,
                                    RuntimeFieldPath path,
                                    String bindingKind,
                                    String authority) {
            this(regionId, root, event, path, bindingKind, authority,
                    null, null, null,
                    Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                    Collections.<RuntimeRegionPlanner.FieldAccessEvent>emptyList());
        }

        private RuntimeFieldBinding(String regionId,
                                    RuntimeRegionPlanner.MethodEvent root,
                                    RuntimeRegionPlanner.FieldAccessEvent event,
                                    RuntimeFieldPath path,
                                    String bindingKind,
                                    String authority,
                                    RuntimeRegionPlanner.FieldAccessEvent containerRead,
                                    RuntimeRegionPlanner.RuntimeEvent mutationEnter,
                                    RuntimeRegionPlanner.RuntimeEvent mutationCompletion,
                                    List<RuntimeRegionPlanner.RuntimeEvent> mutationArguments,
                                    List<RuntimeRegionPlanner.FieldAccessEvent> activationFields) {
            this.regionId = regionId;
            this.root = root;
            this.event = event;
            this.path = path;
            this.bindingKind = bindingKind;
            this.authority = authority;
            this.containerRead = containerRead;
            this.mutationEnter = mutationEnter;
            this.mutationCompletion = mutationCompletion;
            this.mutationArguments = mutationArguments == null
                    ? Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList()
                    : mutationArguments;
            this.activationFields = activationFields == null
                    ? Collections.<RuntimeRegionPlanner.FieldAccessEvent>emptyList()
                    : activationFields;
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
            result.put("boundaryState", "ACTIVATION_LOCAL");
            if (containerRead != null && mutationEnter != null
                    && mutationCompletion != null) {
                result.put("writerFieldReadSeq", containerRead.seq);
                result.put("mutatorEnterSeq", mutationEnter.seq);
                result.put("mutationCompletionSeq", mutationCompletion.seq);
                result.put("mutationInvocationId",
                        mutationEnter.invocationId);
                result.put("mutatorDeclaredCallee",
                        mutationEnter.declaredCallee);
                addAssociativeMemberIdentity(result);
            }
            return result;
        }

        /**
         * Names one map member by its defining mutation, never by its value or
         * iteration position.  Object ids are retained only as trace-local
         * evidence for attaching the member's demanded field leaves.
         */
        private void addAssociativeMemberIdentity(
                Map<String, Object> result) {
            if (!JavaContainerTypes.associativePut(
                    mutationEnter.declaredCallee)
                    || mutationEnter.objectId == 0
                    || mutationEnter.invocationId <= 0L) {
                return;
            }
            RuntimeRegionPlanner.RuntimeEvent key = uniqueArgument(0);
            RuntimeRegionPlanner.RuntimeEvent value = uniqueArgument(1);
            if (key == null || value == null || key.objectId == 0
                    || value.objectId == 0) {
                return;
            }
            result.put("containerMemberToken", associativeMemberToken(
                    root.sourceKey, mutationEnter.objectId,
                    mutationEnter.invocationId));
            result.put("containerMemberIdentityAuthority",
                    ASSOCIATIVE_MEMBER_AUTHORITY);
            result.put("containerObjectId", mutationEnter.objectId);
            result.put("containerKeyObjectId", key.objectId);
            result.put("containerValueObjectId", value.objectId);

            Map<String, RuntimeRegionPlanner.FieldAccessEvent> latest =
                    new LinkedHashMap<>();
            for (RuntimeRegionPlanner.FieldAccessEvent field
                    : activationFields) {
                if (field.seq >= mutationEnter.seq
                        || field.receiverObjectId != value.objectId
                        || field.primitiveValue.isEmpty()) {
                    continue;
                }
                RuntimeRegionPlanner.FieldAccessEvent previous =
                        latest.get(field.field);
                if (previous == null || field.seq > previous.seq) {
                    latest.put(field.field, field);
                }
            }
            List<Map<String, Object>> leaves = new ArrayList<>();
            for (RuntimeRegionPlanner.FieldAccessEvent field
                    : latest.values()) {
                Map<String, Object> leaf = new LinkedHashMap<>();
                leaf.put("field", field.field);
                leaf.put("eventSeq", field.seq);
                leaf.put("callId", field.callId);
                leaf.put("siteId", field.siteId);
                leaf.put("fieldReceiverObjectId",
                        field.receiverObjectId);
                leaves.add(leaf);
            }
            result.put("containerMemberFieldBindings", leaves);
        }

        private RuntimeRegionPlanner.RuntimeEvent uniqueArgument(int index) {
            RuntimeRegionPlanner.RuntimeEvent selected = null;
            for (RuntimeRegionPlanner.RuntimeEvent argument
                    : mutationArguments) {
                if (argument.argumentIndex != index) continue;
                if (selected != null) return null;
                selected = argument;
            }
            return selected;
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
