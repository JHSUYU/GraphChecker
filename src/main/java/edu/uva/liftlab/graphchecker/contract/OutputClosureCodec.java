package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec.DeclaredField;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.validFieldDescriptor;

/**
 * Versioned structural codec for {@link OutputClosureContract}.
 *
 * <p>The codec proves wire shape, invocation identity and direct endpoint
 * consistency.  It intentionally does not repeat Scheduler/Importer dynamic
 * capture and materialization proofs.</p>
 */
public final class OutputClosureCodec {
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
        rejectLegacyMirrors(artifact);
        OutputClosureContract contract =
                decodeEnvelope(encoded.getAsJsonObject());
        validateOuterScope(artifact, contract.producer());
        return contract;
    }

    private static void rejectLegacyMirrors(JsonObject artifact) {
        for (String field : SINGULAR_FIELDS) {
            if (artifact.has(field)) {
                throw new IllegalArgumentException(
                        "explicit outputClosure forbids legacy mirror "
                                + field);
            }
        }
    }

    public static OutputClosureContract decodeEnvelope(JsonObject envelope) {
        requireInt(envelope, "schemaVersion",
                OutputClosureContract.SCHEMA_VERSION);
        requireText(envelope, "kind", OutputClosureContract.KIND);
        JsonObject scope = requireObject(envelope, "producer");
        OutputClosureContract.Producer producer =
                new OutputClosureContract.Producer(
                        requireText(scope, "regionId"),
                        requireText(scope, "regionInstanceId"),
                        requireLong(scope, "rootCallId"));

        List<JsonObject> causalEdges = causalEdges(envelope);
        JsonArray rows = requireArray(envelope, "members");
        if (rows.size() == 0) {
            throw new IllegalArgumentException(
                    "outputClosure.members must not be empty");
        }
        List<OutputClosureContract.Member> members = new ArrayList<>();
        for (int i = 0; i < rows.size(); i++) {
            if (!rows.get(i).isJsonObject()) {
                throw new IllegalArgumentException(
                        "outputClosure.members[" + i + "] must be an object");
            }
            OutputClosureContract.Member member = decodeMember(
                    rows.get(i).getAsJsonObject(), i);
            producer.requireOutputPort(member.portId());
            members.add(member);
        }
        return new OutputClosureContract(producer, members, causalEdges);
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
        Map<String, JsonObject> causalEdges = new LinkedHashMap<>();
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
            for (JsonObject edge : contract.causalEdges()) {
                String id = requireText(edge, "edgeId");
                JsonObject prior = causalEdges.putIfAbsent(id, edge);
                if (prior != null && !CanonicalJson.render(prior)
                        .equals(CanonicalJson.render(edge))) {
                    throw new IllegalArgumentException(
                            "conflicting causal edge " + id);
                }
            }
        }
        return new OutputClosureContract(producer, members.values(),
                causalEdges.values());
    }

    /**
     * Builds one canonical member at the planner boundary.  This is the only
     * supported adapter for producers that still hold their frozen slice as a
     * separate value; it never creates or decodes singular activation mirrors.
     */
    public static OutputClosureContract singleton(
            String regionId, String regionInstanceId, long rootCallId,
            String portId, String cell, String kind,
            String javaType, JsonObject slice) {
        JsonObject normalizedSlice = slice == null
                ? null : slice.deepCopy();
        requireArray(normalizedSlice, "captureBindings");
        JsonArray encodedEdges = requireArray(normalizedSlice,
                "causalEdges");
        List<JsonObject> causalEdges = new ArrayList<>();
        for (int i = 0; i < encodedEdges.size(); i++) {
            if (!encodedEdges.get(i).isJsonObject()) {
                throw new IllegalArgumentException(
                        "causalEdges[" + i + "] must be an object");
            }
            causalEdges.add(encodedEdges.get(i).getAsJsonObject());
        }
        normalizedSlice.remove("causalEdges");
        String descriptor = javaTypeDescriptor(javaType);
        requireFieldDescriptor(descriptor, "requested output");

        JsonObject output = new JsonObject();
        output.addProperty("portId", portId);
        output.addProperty("cell", cell);
        output.addProperty("kind", kind);
        output.addProperty("javaTypeDescriptor", descriptor);
        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", normalizedSlice);

        OutputClosureContract.Producer producer =
                new OutputClosureContract.Producer(regionId,
                        regionInstanceId, rootCallId);
        OutputClosureContract.Member decoded = decodeMember(member, 0);
        producer.requireOutputPort(decoded.portId());
        return new OutputClosureContract(producer,
                Collections.singletonList(decoded), causalEdges);
    }

    public static void writeTo(JsonObject activation,
                               OutputClosureContract contract) {
        if (activation == null || contract == null) {
            throw new IllegalArgumentException(
                    "activation and output closure are required");
        }
        validateOuterScope(activation, contract.producer());
        rejectLegacyMirrors(activation);
        activation.add(OutputClosureContract.FIELD, contract.toJson());
    }

    public static List<OutputCaptureSpec> captureSpecs(
            OutputClosureContract contract) {
        List<OutputCaptureSpec> result = new ArrayList<>();
        for (OutputClosureContract.Member member : contract.members()) {
            for (JsonElement capture : member.captures()) {
                result.add(OutputCaptureSpec.decodeValidated(
                        capture.getAsJsonObject()));
            }
        }
        return Collections.unmodifiableList(result);
    }

    private static OutputClosureContract.Member decodeMember(
            JsonObject encoded, int index) {
        String path = "outputClosure.members[" + index + "]";
        JsonObject output = requireObject(encoded, "output");
        String port = requireText(output, "portId");
        String cell = requireText(output, "cell");
        String kind = requireText(output, "kind");
        if (!OUTPUT_KINDS.contains(kind)) {
            throw new IllegalArgumentException(
                    path + ".output.kind is unsupported: " + kind);
        }
        String descriptor = requireText(output, "javaTypeDescriptor");
        requireFieldDescriptor(descriptor, path);

        JsonObject slice = requireObject(encoded, "slice");
        if (slice.has("causalEdges")) {
            throw new IllegalArgumentException(
                    path + ".slice contains non-canonical causalEdges");
        }
        validateSliceShape(slice, port, cell, path + ".slice");
        JsonArray bindings = requireArray(slice, "captureBindings");
        validateCaptureLedger(bindings, port, cell, path,
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
        requireArray(slice, "captureBindingIssues");
        if (slice.has("captureBindingsComplete")) {
            throw new IllegalArgumentException(
                    path + " contains retired captureBindingsComplete");
        }
        if (slice.has("captureBindingsRequired")) {
            throw new IllegalArgumentException(
                    path + " contains retired captureBindingsRequired");
        }
    }

    private static void validateCaptureLedger(
            JsonArray bindings, String port, String cell,
            String path, String descriptor) {
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
            if (binding.has("captureKind")) {
                throw new IllegalArgumentException(
                        path + " contains retired captureKind");
            }
            validateExitFieldEndpoint(binding, cell, path, descriptor);
        }
    }

    private static void validateExitFieldEndpoint(
            JsonObject binding, String cell, String path,
            String descriptor) {
        DeclaredField field = FieldPathSpec.declaredField(
                requireText(binding, "fieldSignature"));
        List<String> fieldPath = FieldPathSpec.stringArray(binding,
                "fieldPath");
        String javaType = requireText(binding, "javaType");
        if (field == null || !cell.equals(
                requireText(binding, "fieldSignature"))
                || fieldPath.size() != 1
                || !field.name().equals(fieldPath.get(0))
                || !field.type().equals(javaType)
                || !descriptor.equals(javaTypeDescriptor(javaType))) {
            throw new IllegalArgumentException(
                    path + " region-exit field capture is inconsistent");
        }
        requireText(binding, "accessRootInputPort");
    }

    private static void requireFieldDescriptor(String value, String path) {
        if (!validFieldDescriptor(value)) {
            throw new IllegalArgumentException(
                    path + ".javaTypeDescriptor is invalid: " + value);
        }
    }

    private static List<JsonObject> causalEdges(JsonObject envelope) {
        JsonArray encoded = requireArray(envelope, "causalEdges");
        List<JsonObject> result = new ArrayList<>();
        for (int i = 0; i < encoded.size(); i++) {
            if (!encoded.get(i).isJsonObject()) {
                throw new IllegalArgumentException(
                        "causalEdges[" + i + "] must be an object");
            }
            JsonObject edge = encoded.get(i).getAsJsonObject();
            requireText(edge, "edgeId");
            result.add(edge);
        }
        return result;
    }

    private static void validateOuterScope(
            JsonObject activation, OutputClosureContract.Producer producer) {
        if ((activation.has("regionId")
                && !producer.regionId().equals(
                requireText(activation, "regionId")))
                || (activation.has("regionInstanceId")
                && !producer.regionInstanceId().equals(
                requireText(activation, "regionInstanceId")))
                || (activation.has("rootCallId")
                && producer.rootCallId()
                != requireLong(activation, "rootCallId"))) {
            throw new IllegalArgumentException(
                    "outputClosure producer conflicts with artifact scope");
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

    private static void requireInt(
            JsonObject object, String name, int expected) {
        long value = requireLong(object, name);
        if (value != expected) {
            throw new IllegalArgumentException(
                    name + " must be " + expected + ", got " + value);
        }
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
