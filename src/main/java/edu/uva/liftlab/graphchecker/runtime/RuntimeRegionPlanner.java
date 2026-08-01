package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.ToNumberPolicy;
import com.google.gson.reflect.TypeToken;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.lang.reflect.Type;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
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
import java.util.UUID;
import java.util.function.ToLongFunction;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.GZIPInputStream;

/** Binds region skeletons and refined region state to concrete activations. */
final class RuntimeRegionPlanner {
    private static final Type ROW =
            new TypeToken<Map<String, Object>>() { }.getType();
    private static final Gson GSON = new GsonBuilder()
            .setObjectToNumberStrategy(ToNumberPolicy.LONG_OR_DOUBLE)
            .create();
    private static final Pattern FIELD = Pattern.compile(
            "^<[^:]+:\\s+([^()<>]+)\\s+[^\\s()>]+>$");

    private RuntimeRegionPlanner() {
    }

    static Result planSkeletonGraph(File skeletonFile,
                                    List<MethodEvent> methods) {
        List<Map<String, Object>> skeletons = read(skeletonFile);
        for (Map<String, Object> row : skeletons) {
            require(row, 3, "REGION_SKELETON", skeletonFile);
        }
        TraceIndex trace = new TraceIndex(methods, Collections.emptyList(),
                Collections.emptyList());
        Result result = new Result();
        result.staticRegionCount = skeletons.size();
        Map<Long, Map<String, Object>> activationByCall =
                new LinkedHashMap<>();
        for (Map<String, Object> skeleton : skeletons) {
            if ("PROTOCOL_COMPONENT".equals(text(
                    skeleton.get("selection")))) {
                for (MethodEvent anchor : trace.methods(
                        text(skeleton.get("anchorMethod")))) {
                    addSkeletonActivation(result, activationByCall, skeleton,
                            anchor, trace);
                }
                continue;
            }
            String rootMethod = text(skeleton.get("rootMethod"));
            Set<Long> selectedRoots = new LinkedHashSet<>();
            for (MethodEvent root : trace.methods(rootMethod)) {
                if (!trace.methodNames(trace.subtree(root.callId)).contains(
                        text(skeleton.get("anchorMethod")))) {
                    continue;
                }
                addSkeletonActivation(result, activationByCall, skeleton,
                        root, trace);
                selectedRoots.add(root.callId);
            }
            if (!selectedRoots.isEmpty()) {
                continue;
            }
            Set<String> allowed = new LinkedHashSet<>(
                    strings(skeleton.get("methods")));
            for (MethodEvent anchor : trace.methods(
                    text(skeleton.get("anchorMethod")))) {
                MethodEvent root = trace.highestObservedAncestor(anchor,
                        allowed);
                if (root != null && selectedRoots.add(root.callId)) {
                    addSkeletonActivation(result, activationByCall, skeleton,
                            root, trace);
                }
            }
        }
        for (Map.Entry<Long, Map<String, Object>> entry
                : activationByCall.entrySet()) {
            long parent = trace.nearestAncestor(entry.getKey(),
                    activationByCall.keySet());
            if (parent == 0L) {
                continue;
            }
            Map<String, Object> edge = new LinkedHashMap<>();
            edge.put("schemaVersion", 3);
            edge.put("kind", "RUNTIME_ACTIVATION_EDGE");
            edge.put("fromActivation", activationByCall.get(parent).get(
                    "activationId"));
            edge.put("toActivation", entry.getValue().get("activationId"));
            result.runtimeGraphEdges.add(edge);
        }
        return result;
    }

    private static void addSkeletonActivation(
            Result result,
            Map<Long, Map<String, Object>> activationByCall,
            Map<String, Object> skeleton, MethodEvent root,
            TraceIndex trace) {
        Set<Long> calls = trace.subtree(root.callId);
        Set<String> allowed = new LinkedHashSet<>(
                strings(skeleton.get("methods")));
        calls.removeIf(call -> {
            MethodEvent event = trace.methodByCall.get(call);
            return event == null || !allowed.contains(event.method);
        });
        Set<String> observed = trace.methodNames(calls);
        Map<String, Object> activation = new LinkedHashMap<>();
        activation.put("schemaVersion", 3);
        activation.put("kind", "RUNTIME_REGION_ACTIVATION");
        activation.put("activationId", activationId(root));
        activation.put("regionId", skeleton.get("regionId"));
        activation.put("regionIds", Collections.singletonList(
                skeleton.get("regionId")));
        activation.put("rootCallId", root.callId);
        activation.put("rootMethod", root.method);
        activation.put("anchorMethod", skeleton.get("anchorMethod"));
        activation.put("test", root.test);
        activation.put("process", root.process);
        activation.put("thread", root.threadName);
        activation.put("threadId", root.tid);
        activation.put("callIds", new ArrayList<>(calls));
        activation.put("observedMethods", new ArrayList<>(observed));
        result.runtimeInstances.add(activation);
        activationByCall.put(root.callId, activation);
    }

    static Result plan(File regionFile, File regionEdgeFile,
                       File refinedGraphFile, List<MethodEvent> methods,
                       List<RuntimeEvent> runtimeEvents,
                       List<FieldAccessEvent> fieldEvents) {
        requireRefinedGraph(refinedGraphFile);
        List<Map<String, Object>> regions = read(regionFile);
        List<Map<String, Object>> regionEdges = read(regionEdgeFile);
        TraceIndex trace = new TraceIndex(methods, runtimeEvents, fieldEvents);
        Result result = new Result();
        result.staticRegionCount = regions.size();
        Map<String, String> instanceByRegionAndCall = new LinkedHashMap<>();
        for (Map<String, Object> region : regions) {
            require(region, 3, "SYMBOLIC_REGION", regionFile);
            if (!"RUNTIME_REFINED_DATAFLOW".equals(
                    text(region.get("graphKind")))) {
                throw new IllegalArgumentException(
                        "region was not planned from the refined graph: "
                                + regionFile);
            }
            String rootMethod = text(region.get("rootMethod"));
            for (MethodEvent root : trace.methods(rootMethod)) {
                Set<Long> calls = trace.subtree(root.callId);
                Set<String> observedMethods = trace.methodNames(calls);
                if (!observedMethods.contains(text(region.get(
                        "anchorMethod")))) {
                    continue;
                }
                String instanceId = text(region.get("regionId")) + "@"
                        + safe(root.test) + "#call" + root.callId;
                List<Map<String, Object>> symbolize = symbolize(
                        rows(region.get("symbolicInputs")), root.callId);
                List<Map<String, Object>> branches = branches(
                        rows(region.get("branchPolicies")),
                        trace.runtime(calls));
                Map<String, Object> goal = new LinkedHashMap<>();
                goal.put("goalId", "GOAL.TARGET_REACH."
                        + UUID.nameUUIDFromBytes(instanceId.getBytes(
                        StandardCharsets.UTF_8)));
                goal.put("kind", "TARGET_REACH_CLOSURE");
                goal.put("runtimeDefinitionMethods",
                        new ArrayList<>(observedMethods));
                goal.put("admission", object("state", "READY", "mode",
                        "RUNTIME_REFINED_ACTIVATION", "blockers",
                        Collections.emptyList()));
                goal.put("symbolize", symbolize);
                goal.put("branches", branches);
                goal.put("edgeBindings", Collections.emptyList());

                Map<String, Object> plan = new LinkedHashMap<>();
                plan.put("schemaVersion", 3);
                plan.put("kind", "CONCOLIC_REGION_PLAN");
                plan.put("regionInstanceId", instanceId);
                plan.put("regionId", region.get("regionId"));
                plan.put("rootCallId", root.callId);
                plan.put("rootSelector", rootSelector(root,
                        trace.ordinal(root)));
                plan.put("targetMethod", region.get("anchorMethod"));
                plan.put("closureGoals", Collections.singletonList(goal));
                result.regionPlans.add(plan);
                instanceByRegionAndCall.put(instanceKey(
                        text(region.get("regionId")), root.callId),
                        instanceId);
            }
        }
        for (Map<String, Object> edge : regionEdges) {
            String edgeKind = text(edge.get("kind"));
            if (!"RUNTIME_FIELD_FLOW".equals(edgeKind)
                    && !"RUNTIME_PROTOCOL_FLOW".equals(edgeKind)) {
                throw new IllegalArgumentException("invalid runtime region "
                        + "flow row in " + regionEdgeFile);
            }
            String fromInstance = instanceByRegionAndCall.get(instanceKey(
                    text(edge.get("fromRegion")),
                    longNumber(edge.get("fromRootCallId"), -1L)));
            String toInstance = instanceByRegionAndCall.get(instanceKey(
                    text(edge.get("toRegion")),
                    longNumber(edge.get("toRootCallId"), -1L)));
            if (fromInstance == null || toInstance == null) {
                throw new IllegalArgumentException(
                        "runtime field flow has no selected activation: "
                                + text(edge.get("edgeId")));
            }
            boolean protocol = "RUNTIME_PROTOCOL_FLOW".equals(edgeKind);
            Map<String, Object> binding = object(
                    "schemaVersion", 3,
                    "evidenceKind", protocol
                            ? "CONFIGURED_PROTOCOL_TRACE_V1"
                            : "FIELD_ASSIGNMENT_READ_FROM_V1",
                    "fromRegionInstance", fromInstance,
                    "toRegionInstance", toInstance,
                    "fromOutputPort", edge.get("fromPort"),
                    "toInputPort", edge.get("toPort"),
                    "receiverObjectId", edge.get("receiverObjectId"),
                    "writerEventSeq", edge.get("writerEventSeq"),
                    "readerEventSeq", edge.get("readerEventSeq"),
                    "mappingId", edge.get("mappingId"),
                    "wireId", edge.get("wireId"),
                    "sendEventSeq", edge.get("sendEventSeq"),
                    "receiveEventSeq", edge.get("receiveEventSeq"),
                    "protocolDirection", edge.get("direction"),
                    "protocolPort", edge.get("port"),
                    "fieldPathDeclarations",
                    edge.get("fieldPathDeclarations"),
                    "correlationAuthority",
                    protocol ? "CONFIGURED_PROTOCOL_WIRE_ID_V1"
                            : "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
            Map<String, Object> evidence = new LinkedHashMap<>(edge);
            evidence.put("state", protocol
                    ? "CONFIRMED_RUNTIME_PROTOCOL"
                    : "CONFIRMED_RUNTIME_IDENTITY");
            evidence.put("bindings", Collections.singletonList(binding));
            result.edgeValidations.add(evidence);
        }
        return result;
    }

    private static String instanceKey(String region, long rootCallId) {
        return region + "\n" + rootCallId;
    }

    private static List<Map<String, Object>> symbolize(
            List<Map<String, Object>> ports, long rootCallId) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map<String, Object> port : ports) {
            if (longNumber(port.get("rootCallId"), -1L) != rootCallId) {
                continue;
            }
            List<String> path = strings(port.get("fieldPath"));
            Map<String, Object> action = new LinkedHashMap<>(port);
            action.put("symbol", port.get("portId"));
            action.put("observed", true);
            action.put("objectId", port.get("rootObjectId"));
            action.put("javaType", leafType(
                    strings(port.get("fieldPathDeclarations"))));
            if ("PROTOCOL_INPUT".equals(text(port.get("sourceKind")))) {
                if (port.containsKey("argumentIndex")) {
                    action.put("argumentIndex", port.get("argumentIndex"));
                }
                action.put("location", "REQUEST".equals(
                        text(port.get("protocolDirection")))
                        ? "PROTOCOL_ARGUMENT" : "PROTOCOL_RETURN");
            } else if ("PARAMETER".equals(text(port.get("rootKind")))) {
                action.put("argumentIndex", port.get("rootParameterIndex"));
                action.put("location", path.isEmpty()
                        ? "ARGUMENT" : "ARGUMENT_FIELD_PATH");
            } else {
                action.put("location", "RECEIVER_FIELD");
            }
            if (!path.isEmpty()) {
                action.put("fieldPaths",
                        Collections.singletonList(path));
            }
            result.add(action);
        }
        return result;
    }

    private static List<Map<String, Object>> branches(
            List<Map<String, Object>> policies,
            List<RuntimeEvent> events) {
        Map<String, List<RuntimeEvent>> bySite = new LinkedHashMap<>();
        for (RuntimeEvent event : events) {
            if ("BRANCH".equals(event.kind)) {
                bySite.computeIfAbsent(event.siteId,
                        ignored -> new ArrayList<>()).add(event);
            }
        }
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map<String, Object> policy : policies) {
            String site = text(policy.get("siteId"));
            List<RuntimeEvent> occurrences = bySite.getOrDefault(site,
                    Collections.emptyList());
            List<Map<String, Object>> encoded = new ArrayList<>();
            for (int index = 0; index < occurrences.size(); index++) {
                encoded.add(object("occurrence", index + 1, "outcome",
                        occurrences.get(index).outcome));
            }
            RuntimeEvent selected = occurrences.isEmpty() ? null
                    : occurrences.get(occurrences.size() - 1);
            Map<String, Object> branch = new LinkedHashMap<>(policy);
            branch.put("observed", selected != null);
            branch.put("observedOutcome",
                    selected == null ? null : selected.outcome);
            branch.put("selectedOccurrence", occurrences.size());
            branch.put("occurrences", encoded);
            result.add(branch);
        }
        return result;
    }

    private static Map<String, Object> rootSelector(MethodEvent root,
                                                     int ordinal) {
        Map<String, Object> result = new LinkedHashMap<>();
        result.put("method", root.method);
        result.put("ordinal", Math.max(1, ordinal));
        if (root.receiverType.isEmpty()) {
            result.put("kind", "GLOBAL_INVOCATION");
        } else {
            result.put("kind", "RECEIVER_CONTEXT");
            result.put("receiverClass", root.receiverType);
            if (!root.threadName.isEmpty()) {
                result.put("thread", root.threadName);
            }
        }
        return result;
    }

    private static void requireRefinedGraph(File graph) {
        List<Map<String, Object>> rows = read(graph);
        if (rows.isEmpty()) {
            throw new IllegalArgumentException("refined graph is empty: "
                    + graph);
        }
        for (Map<String, Object> row : rows) {
            if (integer(row.get("schemaVersion"), -1) != 3
                    || integer(row.get("refinementSchemaVersion"), -1) != 1
                    || !"RUNTIME_REFINED_DATAFLOW".equals(
                    text(row.get("graphKind")))) {
                throw new IllegalArgumentException(
                        "concolic planning requires the runtime-refined graph: "
                                + graph);
            }
        }
    }

    private static void require(Map<String, Object> row, int schema,
                                String kind, File source) {
        if (integer(row.get("schemaVersion"), -1) != schema
                || !kind.equals(text(row.get("kind")))) {
            throw new IllegalArgumentException("invalid " + kind
                    + " row in " + source);
        }
    }

    private static List<Map<String, Object>> read(File file) {
        if (file == null || !file.isFile()) {
            throw new IllegalArgumentException("artifact is missing: " + file);
        }
        List<Map<String, Object>> result = new ArrayList<>();
        try (BufferedReader reader = reader(file)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (!line.trim().isEmpty()) {
                    Map<String, Object> row = GSON.fromJson(line, ROW);
                    if (row == null) {
                        throw new IllegalArgumentException(
                                "null artifact row: " + file);
                    }
                    result.add(row);
                }
            }
        } catch (IOException failure) {
            throw new IllegalArgumentException("cannot read " + file,
                    failure);
        }
        return result;
    }

    private static BufferedReader reader(File file) throws IOException {
        InputStream input = Files.newInputStream(file.toPath());
        if (file.getName().endsWith(".gz")) {
            input = new GZIPInputStream(input);
        }
        return new BufferedReader(new InputStreamReader(input,
                StandardCharsets.UTF_8));
    }

    private static String activationId(MethodEvent root) {
        return "ACT." + UUID.nameUUIDFromBytes((root.test + "\n"
                + root.process + "\n" + root.tid + "\n" + root.callId)
                .getBytes(StandardCharsets.UTF_8));
    }

    private static String leafType(List<String> declarations) {
        if (declarations.isEmpty()) {
            return "java.lang.Object";
        }
        Matcher matcher = FIELD.matcher(
                declarations.get(declarations.size() - 1));
        return matcher.matches() ? matcher.group(1) : "java.lang.Object";
    }

    private static Map<String, Object> object(Object... fields) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (int index = 0; index + 1 < fields.length; index += 2) {
            result.put(String.valueOf(fields[index]), fields[index + 1]);
        }
        return result;
    }

    @SuppressWarnings("unchecked")
    private static List<Map<String, Object>> rows(Object value) {
        List<Map<String, Object>> result = new ArrayList<>();
        if (value instanceof Collection<?>) {
            for (Object item : (Collection<?>) value) {
                if (item instanceof Map<?, ?>) {
                    result.add((Map<String, Object>) item);
                }
            }
        }
        return result;
    }

    private static List<String> strings(Object value) {
        List<String> result = new ArrayList<>();
        if (value instanceof Collection<?>) {
            for (Object item : (Collection<?>) value) {
                if (!text(item).isEmpty()) {
                    result.add(text(item));
                }
            }
        }
        return result;
    }

    private static int integer(Object value, int fallback) {
        return value instanceof Number ? ((Number) value).intValue()
                : fallback;
    }

    private static long longNumber(Object value, long fallback) {
        return value instanceof Number ? ((Number) value).longValue()
                : fallback;
    }

    private static String text(Object value) {
        return value == null || "null".equals(String.valueOf(value))
                ? "" : String.valueOf(value);
    }

    private static String safe(String value) {
        return value == null ? "" : value;
    }

    private static <T> List<T> sorted(Collection<T> source,
                                      ToLongFunction<T> sequence) {
        List<T> result = new ArrayList<>(source == null
                ? Collections.emptyList() : source);
        result.sort(Comparator.comparingLong(sequence));
        return result;
    }

    static final class Result {
        final List<Map<String, Object>> regionPlans = new ArrayList<>();
        final List<Map<String, Object>> edgeValidations = new ArrayList<>();
        final List<Map<String, Object>> runtimeInstances = new ArrayList<>();
        final List<Map<String, Object>> runtimeGraphEdges = new ArrayList<>();
        int staticRegionCount;

        String regionPlansJsonl() {
            return jsonl(regionPlans);
        }

        String edgeValidationsJsonl() {
            return jsonl(edgeValidations);
        }

        String runtimeInstancesJsonl() {
            return jsonl(runtimeInstances);
        }

        String runtimeGraphEdgesJsonl() {
            return jsonl(runtimeGraphEdges);
        }

        private static String jsonl(List<Map<String, Object>> rows) {
            StringBuilder result = new StringBuilder();
            for (Map<String, Object> row : rows) {
                result.append(GSON.toJson(row)).append('\n');
            }
            return result.toString();
        }
    }

    static final class MethodEvent {
        final long seq;
        final String test;
        final String process;
        final String threadName;
        final long tid;
        final String method;
        final int objectId;
        final String receiverType;
        final long callId;
        final long parentCallId;
        final long parentSiteId;

        MethodEvent(long seq, String test, String process, String threadName,
                    long tid, String method, int objectId, String receiverType,
                    long callId, long parentCallId, long parentSiteId) {
            this.seq = seq;
            this.test = safe(test);
            this.process = safe(process);
            this.threadName = safe(threadName);
            this.tid = tid;
            this.method = safe(method);
            this.objectId = objectId;
            this.receiverType = safe(receiverType);
            this.callId = callId;
            this.parentCallId = parentCallId;
            this.parentSiteId = parentSiteId;
        }
    }

    static final class ProtocolEvent {
        final long seq;
        final String direction;
        final String transport;
        final String wireId;
        final String endpoint;
        final String process;
        final String threadName;
        final long tid;
        final String method;
        final long callId;
        final long invocationId;
        final String declaredCallee;

        ProtocolEvent(long seq, String direction, String transport,
                      String wireId, String endpoint, String process,
                      String threadName, long tid, String method, long callId,
                      long invocationId, String declaredCallee) {
            this.seq = seq;
            this.direction = safe(direction);
            this.transport = safe(transport);
            this.wireId = safe(wireId);
            this.endpoint = safe(endpoint);
            this.process = safe(process);
            this.threadName = safe(threadName);
            this.tid = tid;
            this.method = safe(method);
            this.callId = callId;
            this.invocationId = invocationId;
            this.declaredCallee = safe(declaredCallee);
        }
    }

    static final class RuntimeEvent {
        final long seq;
        final String kind;
        final String method;
        final long callId;
        final long invocationId;
        final long parentSiteId;
        final String siteId;
        final String declaredCallee;
        final int argumentIndex;
        final String runtimeType;
        final int objectId;
        final String primitiveValue;
        final Boolean outcome;
        final Integer successorIndex;
        final String branchKind;
        final String switchCaseKeys;

        RuntimeEvent(long seq, String kind, String method, long callId,
                     long invocationId, long parentSiteId, String siteId,
                     int argumentIndex, String runtimeType, int objectId,
                     String primitiveValue, boolean hasOutcome,
                     boolean outcome) {
            this(seq, kind, method, callId, invocationId, parentSiteId,
                    siteId, "", argumentIndex, runtimeType, objectId,
                    primitiveValue, hasOutcome ? outcome : null, null,
                    "", "");
        }

        RuntimeEvent(long seq, String kind, String method, long callId,
                     long invocationId, long parentSiteId, String siteId,
                     String declaredCallee, int argumentIndex,
                     String runtimeType, int objectId, String primitiveValue,
                     boolean hasOutcome, boolean outcome) {
            this(seq, kind, method, callId, invocationId, parentSiteId,
                    siteId, declaredCallee, argumentIndex, runtimeType,
                    objectId, primitiveValue, hasOutcome ? outcome : null,
                    null, "", "");
        }

        RuntimeEvent(long seq, String kind, String method, long callId,
                     long invocationId, long parentSiteId, String siteId,
                     String declaredCallee, int argumentIndex,
                     String runtimeType, int objectId, String primitiveValue,
                     Boolean outcome, Integer successorIndex, String branchKind,
                     String switchCaseKeys) {
            this.seq = seq;
            this.kind = safe(kind);
            this.method = safe(method);
            this.callId = callId;
            this.invocationId = invocationId;
            this.parentSiteId = parentSiteId;
            this.siteId = safe(siteId);
            this.declaredCallee = safe(declaredCallee);
            this.argumentIndex = argumentIndex;
            this.runtimeType = safe(runtimeType);
            this.objectId = objectId;
            this.primitiveValue = safe(primitiveValue);
            this.outcome = outcome;
            this.successorIndex = successorIndex;
            this.branchKind = safe(branchKind);
            this.switchCaseKeys = safe(switchCaseKeys);
        }
    }

    static final class FieldAccessEvent {
        final long seq;
        final String kind;
        final String method;
        final long callId;
        final int unitIndex;
        final String siteId;
        final String field;
        final int receiverObjectId;
        final int valueObjectId;
        final String primitiveValue;

        FieldAccessEvent(long seq, String kind, String method, long callId,
                         String field, int receiverObjectId,
                         int valueObjectId, String primitiveValue) {
            this(seq, kind, method, callId, -1, "", field,
                    receiverObjectId, valueObjectId, primitiveValue);
        }

        FieldAccessEvent(long seq, String kind, String method, long callId,
                         int unitIndex, String siteId, String field,
                         int receiverObjectId, int valueObjectId,
                         String primitiveValue) {
            this.seq = seq;
            this.kind = safe(kind);
            this.method = safe(method);
            this.callId = callId;
            this.unitIndex = unitIndex;
            this.siteId = unitIndex >= 0 && !this.method.isEmpty()
                    ? this.method + "#u" + unitIndex : safe(siteId);
            this.field = safe(field);
            this.receiverObjectId = receiverObjectId;
            this.valueObjectId = valueObjectId;
            this.primitiveValue = safe(primitiveValue);
        }
    }

    private static final class TraceIndex {
        private final List<MethodEvent> methods;
        private final Map<Long, MethodEvent> methodByCall =
                new LinkedHashMap<>();
        private final Map<String, List<MethodEvent>> methodsByName =
                new LinkedHashMap<>();
        private final Map<Long, List<Long>> children = new LinkedHashMap<>();
        private final Map<Long, List<RuntimeEvent>> runtimeByCall =
                new LinkedHashMap<>();

        private TraceIndex(Collection<MethodEvent> methodEvents,
                           Collection<RuntimeEvent> runtimeEvents,
                           Collection<FieldAccessEvent> ignoredFields) {
            methods = sorted(methodEvents, value -> value.seq);
            for (MethodEvent event : methods) {
                methodByCall.put(event.callId, event);
                methodsByName.computeIfAbsent(event.method,
                        ignored -> new ArrayList<>()).add(event);
                children.computeIfAbsent(event.parentCallId,
                        ignored -> new ArrayList<>()).add(event.callId);
            }
            for (RuntimeEvent event : sorted(runtimeEvents,
                    value -> value.seq)) {
                runtimeByCall.computeIfAbsent(event.callId,
                        ignored -> new ArrayList<>()).add(event);
            }
        }

        private List<MethodEvent> methods(String signature) {
            return methodsByName.getOrDefault(signature,
                    Collections.emptyList());
        }

        private Set<Long> subtree(long root) {
            Set<Long> result = new LinkedHashSet<>();
            Deque<Long> work = new ArrayDeque<>();
            work.add(root);
            while (!work.isEmpty()) {
                long call = work.removeFirst();
                if (result.add(call)) {
                    work.addAll(children.getOrDefault(call,
                            Collections.emptyList()));
                }
            }
            return result;
        }

        private Set<String> methodNames(Set<Long> calls) {
            Set<String> result = new LinkedHashSet<>();
            for (Long call : calls) {
                MethodEvent method = methodByCall.get(call);
                if (method != null) {
                    result.add(method.method);
                }
            }
            return result;
        }

        private List<RuntimeEvent> runtime(Set<Long> calls) {
            List<RuntimeEvent> result = new ArrayList<>();
            for (Long call : calls) {
                result.addAll(runtimeByCall.getOrDefault(call,
                        Collections.emptyList()));
            }
            result.sort(Comparator.comparingLong(value -> value.seq));
            return result;
        }

        private long nearestAncestor(long call, Set<Long> candidates) {
            MethodEvent current = methodByCall.get(call);
            while (current != null && current.parentCallId != 0L) {
                if (candidates.contains(current.parentCallId)) {
                    return current.parentCallId;
                }
                current = methodByCall.get(current.parentCallId);
            }
            return 0L;
        }

        private MethodEvent highestObservedAncestor(MethodEvent start,
                                                    Set<String> allowed) {
            MethodEvent current = start;
            while (current != null) {
                MethodEvent parent = methodByCall.get(current.parentCallId);
                if (parent == null || !allowed.contains(parent.method)) {
                    return current;
                }
                current = parent;
            }
            return start;
        }

        private int ordinal(MethodEvent target) {
            int result = 0;
            for (MethodEvent event : methods) {
                if (event.method.equals(target.method)
                        && event.test.equals(target.test)
                        && event.receiverType.equals(target.receiverType)
                        && event.threadName.equals(target.threadName)) {
                    result++;
                }
                if (event == target) {
                    return Math.max(1, result);
                }
            }
            return 1;
        }
    }
}
