package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.ToNumberPolicy;
import com.google.gson.reflect.TypeToken;
import edu.uva.liftlab.graphchecker.causynth.CausynthJson;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.lang.reflect.Type;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.GZIPInputStream;

/**
 * Refines the cheap static candidate graph with one concrete REGION_STATE
 * execution.  Static discovery chooses methods; receiver/value object identity
 * supplies field paths.  No synthetic access-path cell is created.
 */
final class RuntimeRefinedGraphBuilder {
    static final int REFINEMENT_SCHEMA_VERSION = 1;
    static final String GRAPH_KIND = "RUNTIME_REFINED_DATAFLOW";
    static final String PATH_AUTHORITY =
            "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1";
    static final String FIELD_ACCESS_AUTHORITY =
            "EXACT_RUNTIME_ACTIVATION_FIELD_ACCESS_V1";
    static final String PROTOCOL_AUTHORITY =
            "TRUSTED_CONFIGURED_RPC_MAPPING_V1";
    static final String PROTOCOL_CALLSITE_AUTHORITY =
            "EXACT_RUNTIME_PROTOCOL_CALLSITE_RESULT_V1";

    private static final Type ROW_TYPE =
            new TypeToken<Map<String, Object>>() { }.getType();
    private static final Gson GSON = new GsonBuilder()
            .setObjectToNumberStrategy(ToNumberPolicy.LONG_OR_DOUBLE)
            .create();
    private static final Pattern METHOD = Pattern.compile(
            "^<([^:]+):\\s+(.+)\\s+([^\\s(]+)\\((.*)\\)>$");

    private RuntimeRefinedGraphBuilder() {
    }

    static Result refine(File candidateGraph, File selectedSkeletons,
                         Collection<Map<String, Object>> runtimeInstances,
                         List<RuntimeRegionPlanner.MethodEvent> methods,
                         List<RuntimeRegionPlanner.RuntimeEvent> runtime,
                         List<RuntimeRegionPlanner.FieldAccessEvent> fields,
                         List<RuntimeRegionPlanner.ProtocolEvent> protocol,
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
        List<Map<String, Object>> candidates = readRows(candidateGraph);
        List<RuntimeRegionPlanner.MethodEvent> methodEvents = sortedMethods(
                methods);
        List<RuntimeRegionPlanner.RuntimeEvent> runtimeEvents = sortedRuntime(
                runtime);
        List<RuntimeRegionPlanner.FieldAccessEvent> fieldEvents = sortedFields(
                fields);
        List<RuntimeRegionPlanner.ProtocolEvent> protocolEvents =
                sortedProtocol(protocol);
        ProtocolCallsiteIndex protocolCallsites = new ProtocolCallsiteIndex(
                methodEvents, runtimeEvents);

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
                collectAccessorBindings(activation, activationRuntime,
                        accessorBindingsBySite);
                List<RuntimeRegionPlanner.FieldAccessEvent> activationFields =
                        eventsForCalls(calls, fieldsByCall);
                if (activationFields.isEmpty()) {
                    continue;
                }
                ActivationPaths paths = ActivationPaths.build(root,
                        activationRuntime, activationFields);
                for (RuntimeRegionPlanner.FieldAccessEvent field
                        : activationFields) {
                    StaticSite site = new StaticSite(field.method,
                            field.unitIndex, field.kind, field.field);
                    List<RuntimeFieldPath> fieldPaths = paths.pathsFor(field);
                    boolean boundaryRooted = !fieldPaths.isEmpty();
                    if (!boundaryRooted) {
                        fieldPaths = observedFieldPaths(field);
                    }
                    for (RuntimeFieldPath path : fieldPaths) {
                        bindingsBySite.computeIfAbsent(site,
                                ignored -> new ArrayList<>()).add(
                                new RuntimeFieldBinding(activation.regionId,
                                        root, field, path,
                                        boundaryRooted
                                                ? "DECLARED_FIELD_ACCESS"
                                                : "ACTIVATION_FIELD_ACCESS",
                                        boundaryRooted
                                                ? PATH_AUTHORITY
                                                : FIELD_ACCESS_AUTHORITY));
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
                            : latestContainerFields(activationFields,
                            event.objectId, event.seq)) {
                        String field = container.field;
                        StaticSite site = new StaticSite(event.method,
                                unitIndex, "FIELD_WRITE", field);
                        List<RuntimeFieldPath> containerPaths =
                                paths.pathsFor(container);
                        boolean boundaryRooted = !containerPaths.isEmpty();
                        if (!boundaryRooted) {
                            containerPaths = observedFieldPaths(container);
                        }
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
                                            boundaryRooted
                                                    ? PATH_AUTHORITY
                                                    : FIELD_ACCESS_AUTHORITY,
                                            container, event, completion));
                        }
                    }
                }
        }

        List<Map<String, Object>> refined = new ArrayList<>();
        int runtimeBoundRows = 0;
        for (Map<String, Object> candidate : candidates) {
            requireCandidateEdge(candidate, candidateGraph);
            String method = string(candidate.get("method"));
            String candidateTransfer = string(candidate.get(
                    "transferKind"));
            if (!selectedMethods.contains(method)
                    && !"PROTOCOL_TRANSFER".equals(candidateTransfer)) {
                continue;
            }
            Map<String, Object> edge = new LinkedHashMap<>(candidate);
            edge.put("refinementSchemaVersion", REFINEMENT_SCHEMA_VERSION);
            edge.put("graphKind", GRAPH_KIND);

            String transfer = string(edge.get("transferKind"));
            List<String> regionIds = new ArrayList<>(values(
                    skeletons.regionsByMethod.get(method)));
            if ("PROTOCOL_TRANSFER".equals(transfer)) {
                addAllUnique(regionIds, skeletons.regionsByMethod.get(
                        string(edge.get("protocolClientStub"))));
                addAllUnique(regionIds, skeletons.regionsByMethod.get(
                        string(edge.get("protocolServerStub"))));
            }
            edge.put("regionIds", regionIds);
            if ("accessor_field_return".equals(
                    string(edge.get("kind")))) {
                List<RuntimeAccessorBinding> bindings = values(
                        accessorBindingsBySite.get(AccessorSite.from(edge)));
                if (bindings.isEmpty()) {
                    edge.put("runtimeObserved", false);
                } else {
                    edge.put("runtimeAccessorBindings",
                            encodeAccessorBindings(bindings, edge));
                    edge.put("runtimeObserved", true);
                    runtimeBoundRows++;
                }
            } else if ("HEAP_READ".equals(transfer)
                    || "HEAP_WRITE".equals(transfer)) {
                StaticSite site = StaticSite.from(edge);
                List<RuntimeFieldBinding> bindings = values(
                        bindingsBySite.get(site));
                if (!bindings.isEmpty()) {
                    List<Map<String, Object>> encoded = encodeBindings(bindings);
                    edge.put("runtimeFieldBindings", encoded);
                    List<String> uniquePath = uniquePath(bindings);
                    List<String> uniqueDeclarations =
                            uniqueDeclarations(bindings);
                    if (!uniquePath.isEmpty()) {
                        edge.put("fieldPath", uniquePath);
                        edge.put("fieldPathDeclarations", uniqueDeclarations);
                    }
                    edge.put("runtimeObserved", true);
                    runtimeBoundRows++;
                } else {
                    edge.put("runtimeObserved", false);
                }
            } else if ("PROTOCOL_TRANSFER".equals(transfer)) {
                List<RuntimeProtocolBinding> bindings = protocolBindings(
                        edge, activations, methodEvents, protocolCallsites,
                        protocolEvents);
                if (bindings.isEmpty()) {
                    edge.put("runtimeObserved", false);
                } else {
                    edge.put("runtimeProtocolBindings",
                            encodeProtocolBindings(bindings));
                    for (RuntimeProtocolBinding binding : bindings) {
                        if (!regionIds.contains(binding.from.regionId)) {
                            regionIds.add(binding.from.regionId);
                        }
                        if (!regionIds.contains(binding.to.regionId)) {
                            regionIds.add(binding.to.regionId);
                        }
                    }
                    edge.put("regionIds", regionIds);
                    edge.put("runtimeObserved", true);
                    runtimeBoundRows++;
                }
            } else {
                edge.put("runtimeObserved", true);
            }
            refined.add(edge);
        }

        writeRows(output, refined);
        return new Result(output, refined.size(), runtimeBoundRows,
                activations.size(), selectedMethods.size());
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
                    && event.invocationId > 0L && event.objectId != 0) {
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

    private static List<RuntimeRegionPlanner.FieldAccessEvent>
            latestContainerFields(
            List<RuntimeRegionPlanner.FieldAccessEvent> fields,
            int containerObjectId, long beforeSeq) {
        Map<String, RuntimeRegionPlanner.FieldAccessEvent> selected =
                new LinkedHashMap<>();
        for (RuntimeRegionPlanner.FieldAccessEvent event : fields) {
            if (event.seq > beforeSeq
                    || event.valueObjectId != containerObjectId) {
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

    private static List<RuntimeProtocolBinding> protocolBindings(
            Map<String, Object> edge, List<Activation> activations,
            List<RuntimeRegionPlanner.MethodEvent> methods,
            ProtocolCallsiteIndex callsites,
            List<RuntimeRegionPlanner.ProtocolEvent> events) {
        String transport = string(edge.get("protocolTransport"));
        String clientStub = string(edge.get("protocolClientStub"));
        String serverStub = string(edge.get("protocolServerStub"));
        boolean response = "RESPONSE".equals(
                string(edge.get("protocolDirection")));
        List<RuntimeProtocolBinding> result = new ArrayList<>();
        Set<Long> usedReceives = new LinkedHashSet<>();
        for (RuntimeRegionPlanner.ProtocolEvent send : events) {
            if (!"SEND".equals(send.direction)
                    || !transport.equals(send.transport)) {
                continue;
            }
            RuntimeRegionPlanner.RuntimeEvent callerSite = callsites.find(
                    edge, send);
            if (callerSite == null || callerSite.seq >= send.seq) {
                continue;
            }
            RuntimeRegionPlanner.ProtocolEvent receive = null;
            for (RuntimeRegionPlanner.ProtocolEvent candidate : events) {
                if (!"RECEIVE".equals(candidate.direction)
                        || usedReceives.contains(candidate.seq)
                        || !transport.equals(candidate.transport)
                        || candidate.seq <= send.seq
                        || send.spanId <= 0L
                        || candidate.remoteParentSpanId != send.spanId) {
                    continue;
                }
                receive = candidate;
                break;
            }
            if (receive == null) {
                continue;
            }
            Activation client = activationForCall(activations, send.callId,
                    send.method);
            if (client == null) {
                client = activationForCall(activations, send.callId, "");
            }
            RuntimeRegionPlanner.MethodEvent serverCall = methodForCall(
                    methods, receive.callId, serverStub);
            if (serverCall == null) {
                serverCall = firstMethodAfter(methods, receive, serverStub);
            }
            Activation server = serverCall == null ? null
                    : activationForCall(activations, serverCall.callId,
                    serverStub);
            if (client == null || server == null) {
                continue;
            }
            usedReceives.add(receive.seq);
            result.add(new RuntimeProtocolBinding(edge, send, receive,
                    response ? server : client,
                    response ? client : server, callerSite,
                    callsites.returned(callerSite),
                    response ? callsites.uniqueNormalExit(serverCall.callId)
                            : null));
        }
        return result;
    }

    private static Activation activationForCall(List<Activation> activations,
                                                long callId,
                                                String expectedMethod) {
        for (Activation activation : activations) {
            if (activation.calls.contains(callId)
                    && (expectedMethod == null || expectedMethod.isEmpty()
                    || activation.hasMethod(expectedMethod))) {
                return activation;
            }
        }
        return null;
    }

    private static RuntimeRegionPlanner.MethodEvent methodForCall(
            List<RuntimeRegionPlanner.MethodEvent> methods, long callId,
            String method) {
        if (callId == 0) {
            return null;
        }
        for (RuntimeRegionPlanner.MethodEvent candidate : methods) {
            if (candidate.callId == callId
                    && (method == null || method.isEmpty()
                    || candidate.method.equals(method))) {
                return candidate;
            }
        }
        return null;
    }

    private static RuntimeRegionPlanner.MethodEvent firstMethodAfter(
            List<RuntimeRegionPlanner.MethodEvent> methods,
            RuntimeRegionPlanner.ProtocolEvent receive, String method) {
        for (RuntimeRegionPlanner.MethodEvent candidate : methods) {
            if (candidate.seq > receive.seq && candidate.tid == receive.tid
                    && candidate.process.equals(receive.process)
                    && candidate.method.equals(method)) {
                return candidate;
            }
        }
        return null;
    }

    private static List<Map<String, Object>> encodeProtocolBindings(
            Collection<RuntimeProtocolBinding> bindings) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (RuntimeProtocolBinding binding : bindings) {
            result.add(binding.toMap());
        }
        return result;
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
            Map<String, Object> encoded = binding.toMap();
            unique.put(CausynthJson.write(encoded), encoded);
        }
        return new ArrayList<>(unique.values());
    }

    private static List<Map<String, Object>> encodeAccessorBindings(
            Collection<RuntimeAccessorBinding> bindings,
            Map<String, Object> edge) {
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        for (RuntimeAccessorBinding binding : bindings) {
            Map<String, Object> encoded = binding.toMap(edge);
            unique.put(CausynthJson.write(encoded), encoded);
        }
        return new ArrayList<>(unique.values());
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

    private static List<RuntimeRegionPlanner.ProtocolEvent> sortedProtocol(
            Collection<RuntimeRegionPlanner.ProtocolEvent> events) {
        List<RuntimeRegionPlanner.ProtocolEvent> result = new ArrayList<>(
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
        try (BufferedWriter writer = Files.newBufferedWriter(output,
                StandardCharsets.UTF_8)) {
            for (Map<String, Object> row : rows) {
                writer.write(CausynthJson.write(row));
                writer.write('\n');
            }
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

    private static List<String> parameterTypes(String signature) {
        Matcher matcher = METHOD.matcher(signature);
        if (!matcher.matches() || matcher.group(4).trim().isEmpty()) {
            return Collections.emptyList();
        }
        List<String> result = new ArrayList<>();
        for (String parameter : matcher.group(4).split(",", -1)) {
            result.add(parameter.trim());
        }
        return result;
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
        final int edgeCount;
        final int runtimeBoundEdgeCount;
        final int activationCount;
        final int selectedMethodCount;

        private Result(Path output, int edgeCount, int runtimeBoundEdgeCount,
                       int activationCount,
                       int selectedMethodCount) {
            this.output = output;
            this.edgeCount = edgeCount;
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
        private final Set<String> methods;

        private Activation(Skeleton skeleton,
                           RuntimeRegionPlanner.MethodEvent root,
                           Set<Long> calls) {
            this.regionId = skeleton.regionId;
            this.root = root;
            this.calls = calls;
            this.methods = skeleton.methods;
        }

        private boolean hasMethod(String method) {
            return methods.contains(method);
        }
    }

    private static final class RuntimeProtocolBinding {
        private final Map<String, Object> edge;
        private final RuntimeRegionPlanner.ProtocolEvent send;
        private final RuntimeRegionPlanner.ProtocolEvent receive;
        private final Activation from;
        private final Activation to;
        private final RuntimeRegionPlanner.RuntimeEvent callerSite;
        private final RuntimeRegionPlanner.RuntimeEvent callerResult;
        private final RuntimeRegionPlanner.RuntimeEvent producerResult;

        private RuntimeProtocolBinding(Map<String, Object> edge,
                                       RuntimeRegionPlanner.ProtocolEvent send,
                                       RuntimeRegionPlanner.ProtocolEvent receive,
                                       Activation from, Activation to,
                                       RuntimeRegionPlanner.RuntimeEvent callerSite,
                                       RuntimeRegionPlanner.RuntimeEvent callerResult,
                                       RuntimeRegionPlanner.RuntimeEvent producerResult) {
            this.edge = edge;
            this.send = send;
            this.receive = receive;
            this.from = from;
            this.to = to;
            this.callerSite = callerSite;
            this.callerResult = callerResult;
            this.producerResult = producerResult;
        }

        private Map<String, Object> toMap() {
            Map<String, Object> result = new LinkedHashMap<>();
            result.put("mappingId", edge.get("protocolStubMappingId"));
            result.put("transport", send.transport);
            result.put("direction", edge.get("protocolDirection"));
            result.put("port", edge.get("protocolPort"));
            result.put("fromRegionId", from.regionId);
            result.put("toRegionId", to.regionId);
            result.put("fromRootCallId", from.root.callId);
            result.put("toRootCallId", to.root.callId);
            result.put("fromCell", edge.get("fromCell"));
            result.put("toCell", edge.get("toCell"));
            result.put("callerSiteEventSeq", callerSite.seq);
            result.put("sendEventSeq", send.seq);
            result.put("receiveEventSeq", receive.seq);
            boolean response = "RESPONSE".equals(
                    string(edge.get("protocolDirection")));
            putContext(result, "from", response ? receive : send,
                    from.root);
            putContext(result, "to", response ? send : receive,
                    to.root);
            if (receive.remoteParentSpanId > 0L) {
                result.put("receiveRemoteParentSpanId",
                        receive.remoteParentSpanId);
            }
            result.put("clientCallId", send.callId);
            result.put("serverThreadId", receive.tid);
            result.put("authority", PROTOCOL_AUTHORITY);
            result.put("callsiteAuthority", PROTOCOL_CALLSITE_AUTHORITY);
            result.put("callerMethod", callerSite.method);
            result.put("callerSiteId", callerSite.siteId);
            result.put("callerUnitIndex", unitIndex(callerSite.siteId));
            result.put("callerInvocationId", callerSite.invocationId);
            result.put("callerDeclaredCallee", callerSite.declaredCallee);
            if (callerResult != null && callerResult.objectId != 0) {
                result.put("callerResultObjectId", callerResult.objectId);
                result.put("callerResultRuntimeType",
                        callerResult.runtimeType);
                result.put("callerResultEventSeq", callerResult.seq);
            }
            if (producerResult != null && producerResult.objectId != 0) {
                result.put("producerResultObjectId",
                        producerResult.objectId);
                result.put("producerResultRuntimeType",
                        producerResult.runtimeType);
                result.put("producerResultEventSeq", producerResult.seq);
            }
            int clientIndex = integer(edge.get("protocolClientArgument"),
                    -1);
            int serverIndex = integer(edge.get("protocolServerParameter"),
                    -1);
            if (clientIndex >= 0) {
                result.put("clientArgumentIndex", clientIndex);
            }
            if (serverIndex >= 0) {
                result.put("serverParameterIndex", serverIndex);
            }
            return result;
        }

        private static void putContext(Map<String, Object> target,
                                       String prefix,
                                       RuntimeRegionPlanner.ProtocolEvent event,
                                       RuntimeRegionPlanner.MethodEvent root) {
            long ownerId = event.ownerId > 0L
                    ? event.ownerId : root.ownerId;
            long laneId = event.laneId > 0L ? event.laneId : root.laneId;
            long spanId = event.spanId > 0L ? event.spanId : root.spanId;
            if (ownerId > 0L) {
                target.put(prefix + "OwnerId", ownerId);
            }
            if (laneId > 0L) {
                target.put(prefix + "LaneId", laneId);
            }
            if (spanId > 0L) {
                target.put(prefix + "SpanId", spanId);
            }
        }
    }

    private static final class ProtocolCallsiteIndex {
        private final Map<Long, RuntimeRegionPlanner.MethodEvent> methods =
                new LinkedHashMap<>();
        private final Map<Long, RuntimeRegionPlanner.RuntimeEvent> sitesBySeq =
                new LinkedHashMap<>();
        private final Map<Long, RuntimeRegionPlanner.RuntimeEvent>
                sitesByInvocation = new LinkedHashMap<>();
        private final Map<Long, RuntimeRegionPlanner.RuntimeEvent>
                returnsByInvocation = new LinkedHashMap<>();
        private final Map<Long, List<RuntimeRegionPlanner.RuntimeEvent>>
                normalExitsByCall = new LinkedHashMap<>();
        private ProtocolCallsiteIndex(
                List<RuntimeRegionPlanner.MethodEvent> methodEvents,
                List<RuntimeRegionPlanner.RuntimeEvent> runtimeEvents) {
            for (RuntimeRegionPlanner.MethodEvent method : methodEvents) {
                methods.put(method.callId, method);
            }
            for (RuntimeRegionPlanner.RuntimeEvent event : runtimeEvents) {
                if ("CALL_SITE_ENTER".equals(event.kind)) {
                    sitesBySeq.put(event.seq, event);
                    if (event.invocationId > 0L) {
                        sitesByInvocation.put(event.invocationId, event);
                    }
                } else if ("CALL_SITE_RETURN".equals(event.kind)
                        && event.invocationId > 0L) {
                    returnsByInvocation.put(event.invocationId, event);
                } else if ("METHOD_EXIT_NORMAL".equals(event.kind)
                        && event.callId > 0L) {
                    normalExitsByCall.computeIfAbsent(event.callId,
                            ignored -> new ArrayList<>()).add(event);
                }
            }
        }

        private RuntimeRegionPlanner.RuntimeEvent returned(
                RuntimeRegionPlanner.RuntimeEvent site) {
            return site == null ? null
                    : returnsByInvocation.get(site.invocationId);
        }

        private RuntimeRegionPlanner.RuntimeEvent uniqueNormalExit(
                long callId) {
            List<RuntimeRegionPlanner.RuntimeEvent> exits =
                    normalExitsByCall.getOrDefault(callId,
                            Collections.<RuntimeRegionPlanner.RuntimeEvent>
                                    emptyList());
            return exits.size() == 1 ? exits.get(0) : null;
        }

        private RuntimeRegionPlanner.RuntimeEvent find(
                Map<String, Object> edge,
                RuntimeRegionPlanner.ProtocolEvent send) {
            RuntimeRegionPlanner.RuntimeEvent direct =
                    sitesByInvocation.get(send.invocationId);
            if (matches(edge, direct)) {
                return direct;
            }
            Set<Long> visited = new LinkedHashSet<>();
            RuntimeRegionPlanner.MethodEvent method = methods.get(send.callId);
            while (method != null && visited.add(method.callId)) {
                RuntimeRegionPlanner.RuntimeEvent parent =
                        sitesBySeq.get(method.parentSiteId);
                if (matches(edge, parent)) {
                    return parent;
                }
                method = methods.get(method.parentCallId);
            }
            return null;
        }

        private static boolean matches(Map<String, Object> edge,
                                       RuntimeRegionPlanner.RuntimeEvent site) {
            return site != null
                    && string(edge.get("method")).equals(site.method)
                    && integer(edge.get("unitIndex"), -1)
                    == unitIndex(site.siteId)
                    && string(edge.get("invoke")).equals(
                    site.declaredCallee);
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
            result.put("process", activation.root.process);
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
                                    RuntimeFieldPath path) {
            this(regionId, root, event, path, "DECLARED_FIELD_ACCESS",
                    PATH_AUTHORITY, null, null, null);
        }

        private RuntimeFieldBinding(String regionId,
                                    RuntimeRegionPlanner.MethodEvent root,
                                    RuntimeRegionPlanner.FieldAccessEvent event,
                                    RuntimeFieldPath path,
                                    String bindingKind) {
            this(regionId, root, event, path, bindingKind, PATH_AUTHORITY,
                    null, null, null);
        }

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
            result.put("process", root.process);
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
            result.put("boundaryState", PATH_AUTHORITY.equals(authority)
                    ? "REGION_ROOTED" : "ACTIVATION_LOCAL");
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

    private static final class ActivationPaths {
        private final Map<Integer, Set<RuntimeRoot>> rootsByObject =
                new LinkedHashMap<>();
        private final Map<Integer, Map<String, Integer>> fieldsByReceiver =
                new LinkedHashMap<>();
        private final Map<Long, List<RuntimeFieldPath>> pathsByEvent =
                new LinkedHashMap<>();

        private static ActivationPaths build(
                RuntimeRegionPlanner.MethodEvent root,
                List<RuntimeRegionPlanner.RuntimeEvent> runtime,
                List<RuntimeRegionPlanner.FieldAccessEvent> fields) {
            ActivationPaths result = new ActivationPaths();
            if (root.objectId != 0) {
                result.addRoot(root.objectId, new RuntimeRoot("RECEIVER",
                        root.method, root.method + ".receiver", -1,
                        root.objectId));
            }
            List<String> parameterTypes = parameterTypes(root.method);
            for (RuntimeRegionPlanner.RuntimeEvent event : runtime) {
                if (!"METHOD_ARGUMENT".equals(event.kind)
                        || event.callId != root.callId
                        || event.objectId == 0 || event.argumentIndex < 0) {
                    continue;
                }
                String declaredType = event.argumentIndex < parameterTypes.size()
                        ? parameterTypes.get(event.argumentIndex)
                        : event.runtimeType;
                String cell = root.method + ".param" + event.argumentIndex
                        + ":" + declaredType;
                result.addRoot(event.objectId, new RuntimeRoot("PARAMETER",
                        root.method, cell, event.argumentIndex,
                        event.objectId));
            }

            for (RuntimeRegionPlanner.FieldAccessEvent event : fields) {
                List<RuntimeFieldPath> receiverPaths = result.pathsTo(
                        event.receiverObjectId);
                List<RuntimeFieldPath> eventPaths = new ArrayList<>();
                for (RuntimeFieldPath receiverPath : receiverPaths) {
                    RuntimeFieldPath fieldPath = receiverPath.append(
                            event.field, event.receiverObjectId,
                            event.valueObjectId);
                    if (fieldPath == null) {
                        continue;
                    }
                    eventPaths.add(fieldPath);
                }
                if (!eventPaths.isEmpty()) {
                    result.pathsByEvent.put(event.seq, eventPaths);
                }
                Map<String, Integer> receiverFields =
                        result.fieldsByReceiver.computeIfAbsent(
                                event.receiverObjectId,
                                ignored -> new LinkedHashMap<>());
                if (event.valueObjectId == 0) {
                    receiverFields.remove(event.field);
                } else {
                    receiverFields.put(event.field, event.valueObjectId);
                }
            }
            return result;
        }

        private void addRoot(int objectId, RuntimeRoot root) {
            rootsByObject.computeIfAbsent(objectId,
                    ignored -> new LinkedHashSet<>()).add(root);
        }

        private List<RuntimeFieldPath> pathsTo(int targetObjectId) {
            if (targetObjectId == 0) {
                return Collections.emptyList();
            }
            List<RuntimeFieldPath> result = new ArrayList<>();
            Deque<ObjectPath> work = new ArrayDeque<>();
            for (Map.Entry<Integer, Set<RuntimeRoot>> roots
                    : rootsByObject.entrySet()) {
                for (RuntimeRoot root : roots.getValue()) {
                    work.addLast(new ObjectPath(roots.getKey(),
                            RuntimeFieldPath.root(root)));
                }
            }
            while (!work.isEmpty()) {
                ObjectPath current = work.removeFirst();
                if (current.objectId == targetObjectId) {
                    result.add(current.path);
                }
                for (Map.Entry<String, Integer> field
                        : fieldsByReceiver.getOrDefault(current.objectId,
                        Collections.emptyMap()).entrySet()) {
                    RuntimeFieldPath next = current.path.append(
                            field.getKey(), current.objectId,
                            field.getValue());
                    if (next != null) {
                        work.addLast(new ObjectPath(field.getValue(), next));
                    }
                }
            }
            return result;
        }

        private List<RuntimeFieldPath> pathsFor(
                RuntimeRegionPlanner.FieldAccessEvent event) {
            return values(pathsByEvent.get(event.seq));
        }
    }

    private static final class ObjectPath {
        private final int objectId;
        private final RuntimeFieldPath path;

        private ObjectPath(int objectId, RuntimeFieldPath path) {
            this.objectId = objectId;
            this.path = path;
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
