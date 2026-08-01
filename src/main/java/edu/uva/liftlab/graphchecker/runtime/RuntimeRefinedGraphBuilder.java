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

    private static final Type ROW_TYPE =
            new TypeToken<Map<String, Object>>() { }.getType();
    private static final Gson GSON = new GsonBuilder()
            .setObjectToNumberStrategy(ToNumberPolicy.LONG_OR_DOUBLE)
            .create();
    private static final Pattern FIELD = Pattern.compile(
            "^<([^:]+):\\s+([^()<>]+)\\s+([^\\s()>]+)>$");
    private static final Pattern METHOD = Pattern.compile(
            "^<([^:]+):\\s+(.+)\\s+([^\\s(]+)\\((.*)\\)>$");

    private RuntimeRefinedGraphBuilder() {
    }

    static Result refine(File candidateGraph, File selectedSkeletons,
                         List<RuntimeRegionPlanner.MethodEvent> methods,
                         List<RuntimeRegionPlanner.RuntimeEvent> runtime,
                         List<RuntimeRegionPlanner.FieldAccessEvent> fields,
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

        Map<Long, List<Long>> children = new LinkedHashMap<>();
        for (RuntimeRegionPlanner.MethodEvent event : methodEvents) {
            children.computeIfAbsent(event.parentCallId,
                    ignored -> new ArrayList<>()).add(event.callId);
        }
        Map<Long, List<RuntimeRegionPlanner.RuntimeEvent>> runtimeByCall =
                groupRuntime(runtimeEvents);
        Map<Long, List<RuntimeRegionPlanner.FieldAccessEvent>> fieldsByCall =
                groupFields(fieldEvents);

        Map<StaticSite, List<RuntimeFieldBinding>> bindingsBySite =
                new LinkedHashMap<>();
        int activationCount = 0;
        for (RuntimeRegionPlanner.MethodEvent root : methodEvents) {
            if (!skeletons.roots.contains(root.method)) {
                continue;
            }
            Set<Long> calls = callSubtree(root.callId, children);
            List<RuntimeRegionPlanner.FieldAccessEvent> activationFields =
                    eventsForCalls(calls, fieldsByCall);
            if (activationFields.isEmpty()) {
                continue;
            }
            List<RuntimeRegionPlanner.RuntimeEvent> activationRuntime =
                    eventsForCalls(calls, runtimeByCall);
            ActivationPaths paths = ActivationPaths.build(root,
                    activationRuntime, activationFields);
            for (RuntimeRegionPlanner.FieldAccessEvent field : activationFields) {
                StaticSite site = new StaticSite(field.method,
                        field.unitIndex, field.kind, field.field);
                for (RuntimeFieldPath path : paths.pathsFor(field)) {
                    bindingsBySite.computeIfAbsent(site,
                            ignored -> new ArrayList<>()).add(
                            new RuntimeFieldBinding(root, field, path));
                }
            }
            activationCount++;
        }

        List<Map<String, Object>> refined = new ArrayList<>();
        int runtimeBoundRows = 0;
        for (Map<String, Object> candidate : candidates) {
            requireCandidateEdge(candidate, candidateGraph);
            String method = string(candidate.get("method"));
            if (!selectedMethods.contains(method)) {
                continue;
            }
            Map<String, Object> edge = new LinkedHashMap<>(candidate);
            edge.put("refinementSchemaVersion", REFINEMENT_SCHEMA_VERSION);
            edge.put("graphKind", GRAPH_KIND);
            edge.put("regionIds", skeletons.regionsByMethod.get(method));

            String transfer = string(edge.get("transferKind"));
            if ("HEAP_READ".equals(transfer)
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
            } else {
                edge.put("runtimeObserved", true);
            }
            refined.add(edge);
        }

        writeRows(output, refined);
        return new Result(output, refined.size(), runtimeBoundRows,
                activationCount, selectedMethods.size());
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

    private static Set<Long> callSubtree(long root,
                                         Map<Long, List<Long>> children) {
        Set<Long> result = new LinkedHashSet<>();
        Deque<Long> work = new ArrayDeque<>();
        work.add(root);
        while (!work.isEmpty()) {
            long current = work.removeFirst();
            if (!result.add(current)) {
                continue;
            }
            work.addAll(values(children.get(current)));
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
        try (BufferedWriter writer = Files.newBufferedWriter(output,
                StandardCharsets.UTF_8)) {
            for (Map<String, Object> row : rows) {
                writer.write(CausynthJson.write(row));
                writer.write('\n');
            }
        }
    }

    private static String fieldName(String declaration) {
        Matcher matcher = FIELD.matcher(declaration);
        return matcher.matches() ? matcher.group(3) : "";
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
                for (Object value : (Collection<?>) methods) {
                    String method = string(value);
                    if (method.isEmpty()) {
                        continue;
                    }
                    result.methods.add(method);
                    result.regionsByMethod.computeIfAbsent(method,
                            ignored -> new ArrayList<>()).add(region);
                }
            }
            if (result.methods.isEmpty()) {
                throw new IOException("selected skeletons contain no methods: "
                        + file);
            }
            return result;
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

    private static final class RuntimeFieldBinding {
        private final RuntimeRegionPlanner.MethodEvent root;
        private final RuntimeRegionPlanner.FieldAccessEvent event;
        private final RuntimeFieldPath path;

        private RuntimeFieldBinding(RuntimeRegionPlanner.MethodEvent root,
                                    RuntimeRegionPlanner.FieldAccessEvent event,
                                    RuntimeFieldPath path) {
            this.root = root;
            this.event = event;
            this.path = path;
        }

        private Map<String, Object> toMap() {
            Map<String, Object> result = new LinkedHashMap<>();
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
            result.put("valueFingerprint", event.valueFingerprint);
            result.put("fieldPath", path.fieldNames());
            result.put("fieldPathDeclarations", path.fieldDeclarations());
            result.put("authority", PATH_AUTHORITY);
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
