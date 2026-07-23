package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * Versioned structural codec for {@link OutputClosureContract}.
 *
 * <p>The codec proves wire shape, invocation identity and direct endpoint
 * consistency.  It intentionally does not repeat Scheduler/Importer dynamic
 * capture and materialization proofs.</p>
 */
public final class OutputClosureCodec {
    private static final int MAX_MEMBERS = 128;
    private static final int MAX_DESCRIPTOR_LENGTH = 1024;
    private static final Set<String> ENVELOPE_KEYS = set(
            "schemaVersion", "kind", "producer", "members");
    private static final Set<String> PRODUCER_KEYS = set(
            "regionId", "regionInstanceId", "rootCallId");
    private static final Set<String> MEMBER_KEYS = set(
            "output", "slice");
    private static final Set<String> OUTPUT_KEYS = set(
            "portId", "cell", "kind", "javaTypeDescriptor",
            "selectionAuthority");
    private static final Set<String> OUTPUT_KINDS = set(
            "REGION_OUTPUT", "SINK_STATE", "HEAP_STATE",
            "FAILURE_PREDICATE", "RETURN");
    private static final Set<String> SINGULAR_FIELDS = set(
            "requestedOutput", "requestedOutputSlice",
            "requestedOutputCapture", "requestedOutputCaptureRequired",
            "requestedOutputCaptureComplete", "requestedOutputMethods",
            "outputs");
    private static final List<String> SCOPE_ARRAYS = Arrays.asList(
            "inputPorts", "sites", "staticSites", "methods",
            "causalEdgeIds");

    private OutputClosureCodec() {
    }

    public static OutputClosureContract decode(JsonObject artifact) {
        if (artifact == null) {
            throw new IllegalArgumentException(
                    "output closure artifact is required");
        }
        JsonElement encoded = artifact.get(OutputClosureContract.FIELD);
        if (encoded == null) {
            throw new IllegalArgumentException(
                    "canonical outputClosure is required");
        }
        if (!encoded.isJsonObject()) {
            throw new IllegalArgumentException(
                    "outputClosure must be an object");
        }
        for (String field : SINGULAR_FIELDS) {
            if (artifact.has(field)) {
                throw new IllegalArgumentException(
                        "explicit outputClosure forbids legacy mirror "
                                + field);
            }
        }
        OutputClosureContract contract =
                decodeEnvelope(encoded.getAsJsonObject());
        validateOuterScope(artifact, contract.producer(), false);
        return contract;
    }

    public static OutputClosureContract decodeEnvelope(JsonObject envelope) {
        exactKeys(envelope, ENVELOPE_KEYS, "outputClosure");
        requireInt(envelope, "schemaVersion",
                OutputClosureContract.SCHEMA_VERSION);
        requireText(envelope, "kind", OutputClosureContract.KIND);
        JsonObject scope = requireObject(envelope, "producer");
        exactKeys(scope, PRODUCER_KEYS, "outputClosure.producer");
        OutputClosureContract.Producer producer =
                new OutputClosureContract.Producer(
                        requireText(scope, "regionId"),
                        requireText(scope, "regionInstanceId"),
                        requireLong(scope, "rootCallId"));

        JsonArray rows = requireArray(envelope, "members");
        if (rows.size() == 0 || rows.size() > MAX_MEMBERS) {
            throw new IllegalArgumentException(
                    "outputClosure.members must contain 1.." + MAX_MEMBERS
                            + " members");
        }
        List<OutputClosureContract.Member> members = new ArrayList<>();
        String previous = "";
        for (int i = 0; i < rows.size(); i++) {
            if (!rows.get(i).isJsonObject()) {
                throw new IllegalArgumentException(
                        "outputClosure.members[" + i + "] must be an object");
            }
            OutputClosureContract.Member member = decodeMember(
                    rows.get(i).getAsJsonObject(), i);
            if (!previous.isEmpty()
                    && previous.compareTo(member.portId()) >= 0) {
                throw new IllegalArgumentException(
                        "outputClosure.members must be strictly sorted by "
                                + "portId");
            }
            producer.requireOutputPort(member.portId());
            previous = member.portId();
            members.add(member);
        }
        OutputClosureContract result =
                new OutputClosureContract(producer, members);
        if (!result.supportedJointCapture()) {
            throw new IllegalArgumentException(
                    "multi-output V1 requires one direct primitive capture "
                            + "per member");
        }
        return result;
    }

    /**
     * Combines already decoded singleton contracts without hand-building JSON.
     * Exact duplicate members collapse; conflicting duplicates fail closed.
     */
    public static OutputClosureContract merge(
            Collection<OutputClosureContract> contracts) {
        if (contracts == null || contracts.isEmpty()) {
            throw new IllegalArgumentException(
                    "at least one output closure is required");
        }
        OutputClosureContract.Producer producer = null;
        Map<String, OutputClosureContract.Member> members =
                new LinkedHashMap<>();
        for (OutputClosureContract contract : contracts) {
            if (contract == null) {
                throw new IllegalArgumentException(
                        "output closure must not be null");
            }
            if (producer == null) producer = contract.producer();
            else if (!producer.sameAs(contract.producer())) {
                throw new IllegalArgumentException(
                        "cannot merge different producer invocations");
            }
            for (OutputClosureContract.Member member : contract.members()) {
                OutputClosureContract.Member prior =
                        members.putIfAbsent(member.portId(), member);
                if (prior != null && !CanonicalJson.render(prior.toJson())
                        .equals(CanonicalJson.render(member.toJson()))) {
                    throw new IllegalArgumentException(
                            "conflicting output member " + member.portId());
                }
            }
        }
        OutputClosureContract result =
                new OutputClosureContract(producer, members.values());
        if (!result.supportedJointCapture()) {
            throw new IllegalArgumentException(
                    "merged output closure is outside V1 joint scope");
        }
        return result;
    }

    /**
     * Builds one canonical member at the planner boundary.  This is the only
     * supported adapter for producers that still hold their frozen slice as a
     * separate value; it never creates or decodes singular activation mirrors.
     */
    public static OutputClosureContract singleton(
            String regionId, String regionInstanceId, long rootCallId,
            String portId, String cell, String kind,
            String selectionAuthority, JsonObject slice) {
        JsonObject normalizedSlice = slice == null
                ? null : slice.deepCopy();
        JsonArray bindings = requireArray(normalizedSlice,
                "captureBindings");
        String descriptor = inferDescriptor(cell, kind, bindings);
        if (descriptor.isEmpty()) {
            throw new IllegalArgumentException(
                    "requested output Java type is unknown");
        }

        JsonObject output = new JsonObject();
        output.addProperty("portId", portId);
        output.addProperty("cell", cell);
        output.addProperty("kind", kind);
        output.addProperty("javaTypeDescriptor", descriptor);
        output.addProperty("selectionAuthority", selectionAuthority);
        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", normalizedSlice);

        JsonObject producer = new JsonObject();
        producer.addProperty("regionId", regionId);
        producer.addProperty("regionInstanceId", regionInstanceId);
        producer.addProperty("rootCallId", rootCallId);
        JsonArray members = new JsonArray();
        members.add(member);
        JsonObject envelope = new JsonObject();
        envelope.addProperty("schemaVersion",
                OutputClosureContract.SCHEMA_VERSION);
        envelope.addProperty("kind", OutputClosureContract.KIND);
        envelope.add("producer", producer);
        envelope.add("members", members);
        return decodeEnvelope(envelope);
    }

    public static void writeTo(JsonObject activation,
                               OutputClosureContract contract) {
        if (activation == null || contract == null) {
            throw new IllegalArgumentException(
                    "activation and output closure are required");
        }
        validateOuterScope(activation, contract.producer(), true);
        for (String field : SINGULAR_FIELDS) activation.remove(field);
        activation.add(OutputClosureContract.FIELD, contract.toJson());
    }

    public static JsonArray captures(OutputClosureContract contract) {
        JsonArray result = new JsonArray();
        for (OutputClosureContract.Member member : contract.members()) {
            for (JsonElement capture : member.captures()) {
                result.add(capture.deepCopy());
            }
        }
        return result;
    }

    public static JsonArray executionOutputs(
            OutputClosureContract contract) {
        JsonArray result = new JsonArray();
        for (OutputClosureContract.Member member : contract.members()) {
            result.add(member.executionOutput());
        }
        return result;
    }

    private static OutputClosureContract.Member decodeMember(
            JsonObject encoded, int index) {
        String path = "outputClosure.members[" + index + "]";
        exactKeys(encoded, MEMBER_KEYS, path);
        JsonObject output = requireObject(encoded, "output");
        exactKeys(output, OUTPUT_KEYS, path + ".output");
        String port = requireText(output, "portId");
        String cell = requireText(output, "cell");
        String kind = requireText(output, "kind");
        if (!OUTPUT_KINDS.contains(kind)) {
            throw new IllegalArgumentException(
                    path + ".output.kind is unsupported: " + kind);
        }
        String descriptor = requireText(output, "javaTypeDescriptor");
        requireFieldDescriptor(descriptor, path);
        requireText(output, "selectionAuthority");

        JsonObject slice = requireObject(encoded, "slice");
        validateSliceShape(slice, port, cell, path + ".slice");
        boolean required = requireBoolean(slice, "captureBindingsRequired");
        JsonArray bindings = requireArray(slice, "captureBindings");
        validateCaptureLedger(bindings, required, port, cell, path,
                descriptor);
        return new OutputClosureContract.Member(output, slice);
    }

    private static void validateSliceShape(
            JsonObject slice, String port, String cell, String path) {
        if (!port.equals(requireText(slice, "outputPort"))
                || !cell.equals(requireText(slice, "outputCell"))) {
            throw new IllegalArgumentException(
                    path + " output identity mismatch");
        }
        for (String name : SCOPE_ARRAYS) stringSet(slice, name);
        requireArray(slice, "captureBindings");
        requireBoolean(slice, "captureBindingsRequired");
        requireBoolean(slice, "captureBindingsComplete");
    }

    private static void validateCaptureLedger(
            JsonArray bindings, boolean required, String port, String cell,
            String path, String descriptor) {
        if (required != (bindings.size() > 0)) {
            throw new IllegalArgumentException(
                    path + " capture ledger is inconsistent");
        }
        Set<String> ids = new LinkedHashSet<>();
        for (int i = 0; i < bindings.size(); i++) {
            if (!bindings.get(i).isJsonObject()) {
                throw new IllegalArgumentException(
                        path + ".capture.bindings[" + i
                                + "] must be an object");
            }
            JsonObject binding = bindings.get(i).getAsJsonObject();
            if (!port.equals(requireText(binding, "outputPort"))
                    || !cell.equals(requireText(binding, "outputCell"))
                    || !ids.add(requireText(binding, "captureBindingId"))) {
                throw new IllegalArgumentException(
                        path + " capture identity is inconsistent");
            }
            String captureKind = requireText(binding, "captureKind");
            if ("FIELD_ASSIGNMENT_RHS".equals(captureKind)) {
                validateFieldEndpoint(binding, cell, path);
            } else if ("CALL_ARGUMENT".equals(captureKind)) {
                validateCallEndpoint(binding, cell, descriptor, path);
            }
        }
    }

    private static void validateFieldEndpoint(
            JsonObject binding, String cell, String path) {
        String method = requireText(binding, "method");
        int unit = requireNonNegativeInt(binding, "unitIndex");
        if (!requireText(binding, "siteId").equals(method + "#u" + unit)
                || !cell.equals(requireText(binding, "fieldSignature"))) {
            throw new IllegalArgumentException(
                    path + " field capture endpoint is inconsistent");
        }
    }

    private static void validateCallEndpoint(
            JsonObject binding, String cell, String descriptor, String path) {
        String caller = requireText(binding, "callerMethod");
        int unit = requireNonNegativeInt(binding, "unitIndex");
        String callee = requireText(binding, "calleeMethod");
        int argument = requireNonNegativeInt(binding, "argumentIndex");
        String formalPrefix = callee + ".param" + argument + ":";
        String formalType = cell.startsWith(formalPrefix)
                ? cell.substring(formalPrefix.length()).trim() : "";
        String parameterType = methodParameterType(callee, argument);
        String endpointDescriptor = javaTypeDescriptor(formalType);
        if (!requireText(binding, "siteId").equals(caller + "#u" + unit)
                || formalType.isEmpty()
                || !formalType.equals(parameterType)
                || !descriptor.equals(endpointDescriptor)) {
            throw new IllegalArgumentException(
                    path + " call capture endpoint is inconsistent");
        }
        requireText(binding, "argumentCell");
    }

    private static String inferDescriptor(
            String cell, String kind, JsonArray bindings) {
        if ("FAILURE_PREDICATE".equals(kind)) return "Z";
        String type = typeFromCell(cell);
        if (type.isEmpty() && bindings.size() == 1) {
            JsonObject binding = bindings.get(0).getAsJsonObject();
            type = "CALL_ARGUMENT".equals(text(binding, "captureKind"))
                    ? methodParameterType(text(binding, "calleeMethod"),
                    requireNonNegativeInt(binding, "argumentIndex"))
                    : typeFromCell(text(binding, "fieldSignature"));
        }
        return javaTypeDescriptor(type);
    }

    private static String typeFromCell(String cell) {
        String value = OutputClosureContract.trim(cell);
        int projection = value.indexOf("#field:");
        if (projection >= 0) value = value.substring(0, projection);
        if (value.endsWith(".return")) {
            return methodReturnType(value.substring(
                    0, value.length() - ".return".length()));
        }
        int parameter = value.lastIndexOf(".param");
        int colon = parameter < 0 ? -1 : value.indexOf(':', parameter);
        if (colon >= 0) {
            int end = value.indexOf('#', colon + 1);
            return value.substring(colon + 1,
                    end < 0 ? value.length() : end).trim();
        }
        if (value.startsWith("<") && value.endsWith(">")) {
            int colonIndex = value.indexOf(':');
            int name = value.lastIndexOf(' ');
            if (colonIndex >= 0 && name > colonIndex
                    && value.indexOf('(', name) < 0) {
                return value.substring(colonIndex + 1, name).trim();
            }
        }
        return "";
    }

    private static String methodReturnType(String method) {
        int colon = method.indexOf(':');
        int start = colon + 1;
        while (start < method.length()
                && Character.isWhitespace(method.charAt(start))) start++;
        int space = method.indexOf(' ', start);
        return method.startsWith("<") && method.endsWith(">")
                && colon >= 0 && space > start
                ? method.substring(start, space).trim() : "";
    }

    private static String methodParameterType(String method, int index) {
        if (index < 0) return "";
        int open = method.indexOf('(');
        int close = method.lastIndexOf(')');
        if (!method.startsWith("<") || !method.endsWith(">")
                || open < 0 || close <= open) {
            return "";
        }
        String content = method.substring(open + 1, close).trim();
        if (content.isEmpty()) return "";
        String[] parameters = content.split(",", -1);
        return index < parameters.length ? parameters[index].trim() : "";
    }

    private static String javaTypeDescriptor(String javaType) {
        String value = OutputClosureContract.trim(javaType);
        int dimensions = 0;
        while (value.endsWith("[]") && dimensions < 255) {
            dimensions++;
            value = value.substring(0, value.length() - 2).trim();
        }
        String base;
        if ("boolean".equals(value)) base = "Z";
        else if ("byte".equals(value)) base = "B";
        else if ("char".equals(value)) base = "C";
        else if ("short".equals(value)) base = "S";
        else if ("int".equals(value)) base = "I";
        else if ("long".equals(value)) base = "J";
        else if ("float".equals(value)) base = "F";
        else if ("double".equals(value)) base = "D";
        else if ("void".equals(value)) return "";
        else if (sourceClassName(value)) {
            base = "L" + value.replace('.', '/') + ";";
        } else {
            return "";
        }
        StringBuilder result = new StringBuilder(dimensions + base.length());
        for (int i = 0; i < dimensions; i++) result.append('[');
        result.append(base);
        return validFieldDescriptor(result.toString())
                ? result.toString() : "";
    }

    private static boolean sourceClassName(String value) {
        if (value.isEmpty() || value.length() > MAX_DESCRIPTOR_LENGTH - 2) {
            return false;
        }
        boolean component = false;
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            if (c == '.' || c == '/') {
                if (!component) return false;
                component = false;
            } else if (c <= ' ' || c == ';' || c == '[') {
                return false;
            } else {
                component = true;
            }
        }
        return component;
    }

    static boolean validFieldDescriptor(String value) {
        if (value == null || value.isEmpty()
                || value.length() > MAX_DESCRIPTOR_LENGTH) {
            return false;
        }
        int cursor = 0;
        int dimensions = 0;
        while (cursor < value.length() && value.charAt(cursor) == '[') {
            if (++dimensions > 255) return false;
            cursor++;
        }
        if (cursor >= value.length()) return false;
        char type = value.charAt(cursor++);
        if ("ZBCSIJFD".indexOf(type) >= 0) {
            return cursor == value.length();
        }
        if (type != 'L') return false;
        boolean component = false;
        for (; cursor < value.length(); cursor++) {
            char c = value.charAt(cursor);
            if (c == ';') return component && cursor + 1 == value.length();
            if (c == '/') {
                if (!component) return false;
                component = false;
            } else if (c <= ' ' || c == '.' || c == '[') {
                return false;
            } else {
                component = true;
            }
        }
        return false;
    }

    private static void requireFieldDescriptor(String value, String path) {
        if (!validFieldDescriptor(value)) {
            throw new IllegalArgumentException(
                    path + ".javaTypeDescriptor is invalid: " + value);
        }
    }

    private static void validateOuterScope(
            JsonObject activation, OutputClosureContract.Producer producer,
            boolean required) {
        boolean any = activation.has("regionId")
                || activation.has("regionInstanceId")
                || activation.has("rootCallId");
        if (required || any) {
            if (!producer.regionId().equals(
                    requireText(activation, "regionId"))
                    || !producer.regionInstanceId().equals(
                    requireText(activation, "regionInstanceId"))
                    || producer.rootCallId()
                    != requireLong(activation, "rootCallId")) {
                throw new IllegalArgumentException(
                        "outputClosure producer conflicts with activation");
            }
        }
    }

    private static Set<String> stringSet(JsonObject object, String name) {
        Set<String> result = new LinkedHashSet<>();
        JsonArray values = requireArray(object, name);
        for (int i = 0; i < values.size(); i++) {
            JsonElement value = values.get(i);
            if (!value.isJsonPrimitive()
                    || !value.getAsJsonPrimitive().isString()) {
                throw new IllegalArgumentException(
                        name + "[" + i + "] must be a string");
            }
            String text = value.getAsString().trim();
            if (text.isEmpty() || !result.add(text)) {
                throw new IllegalArgumentException(
                        name + " has an empty or duplicate value");
            }
        }
        return result;
    }

    private static void exactKeys(
            JsonObject object, Set<String> expected, String path) {
        if (object == null || !object.keySet().equals(expected)) {
            TreeSet<String> missing = new TreeSet<>(expected);
            missing.removeAll(object == null
                    ? Collections.<String>emptySet() : object.keySet());
            TreeSet<String> extra = new TreeSet<>(object == null
                    ? Collections.<String>emptySet() : object.keySet());
            extra.removeAll(expected);
            throw new IllegalArgumentException(path
                    + " keys mismatch; missing=" + missing
                    + ", extra=" + extra);
        }
    }

    private static JsonObject requireObject(JsonObject object, String name) {
        JsonElement value = object == null ? null : object.get(name);
        if (value == null || !value.isJsonObject()) {
            throw new IllegalArgumentException(name + " must be an object");
        }
        return value.getAsJsonObject();
    }

    private static JsonArray requireArray(JsonObject object, String name) {
        JsonElement value = object == null ? null : object.get(name);
        if (value == null || !value.isJsonArray()) {
            throw new IllegalArgumentException(name + " must be an array");
        }
        return value.getAsJsonArray();
    }

    private static String requireText(JsonObject object, String name) {
        String value = text(object, name);
        if (value.isEmpty()) {
            throw new IllegalArgumentException(
                    name + " must be a non-empty string");
        }
        return value;
    }

    private static void requireText(
            JsonObject object, String name, String expected) {
        String value = requireText(object, name);
        if (!expected.equals(value)) {
            throw new IllegalArgumentException(
                    name + " must be " + expected + ", got " + value);
        }
    }

    private static boolean requireBoolean(JsonObject object, String name) {
        JsonElement value = object == null ? null : object.get(name);
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isBoolean()) {
            throw new IllegalArgumentException(name + " must be a boolean");
        }
        return value.getAsBoolean();
    }

    private static void requireInt(
            JsonObject object, String name, int expected) {
        long value = requireLong(object, name);
        if (value != expected) {
            throw new IllegalArgumentException(
                    name + " must be " + expected + ", got " + value);
        }
    }

    private static int requireNonNegativeInt(
            JsonObject object, String name) {
        long value = requireLong(object, name);
        if (value < 0 || value > Integer.MAX_VALUE) {
            throw new IllegalArgumentException(
                    name + " must be a non-negative integer");
        }
        return (int) value;
    }

    private static long requireLong(JsonObject object, String name) {
        JsonElement value = object == null ? null : object.get(name);
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isNumber()) {
            throw new IllegalArgumentException(name + " must be an integer");
        }
        try {
            String encoded = value.getAsJsonPrimitive().toString();
            if (encoded.indexOf('.') >= 0 || encoded.indexOf('e') >= 0
                    || encoded.indexOf('E') >= 0) {
                throw new NumberFormatException("not integral");
            }
            return Long.parseLong(encoded);
        } catch (RuntimeException malformed) {
            throw new IllegalArgumentException(
                    name + " must be an integer", malformed);
        }
    }

    private static String text(JsonObject object, String name) {
        return OutputClosureContract.text(object, name);
    }

    private static Set<String> set(String... values) {
        return Collections.unmodifiableSet(
                new LinkedHashSet<>(Arrays.asList(values)));
    }
}
