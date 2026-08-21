package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec.DeclaredField;

import java.nio.charset.StandardCharsets;
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
import java.util.UUID;

import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.validFieldDescriptor;

/**
 * Versioned structural codec for {@link OutputClosureContract}.
 *
 * <p>The codec proves wire shape, relation identity and direct endpoint
 * consistency. Dynamic occurrence identity belongs to the causal skeleton,
 * not to this reusable relation contract.</p>
 */
public final class OutputClosureCodec {
    private static final Set<String> OUTPUT_KINDS = set(
            "REGION_OUTPUT", "SINK_STATE", "HEAP_STATE",
            "FAILURE_PREDICATE", "RETURN", "INTERACTION_EVENT");
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
        OutputClosureContract contract =
                decodeEnvelope(encoded.getAsJsonObject());
        validateOuterScope(artifact, contract.producer());
        return contract;
    }

    public static OutputClosureContract decodeEnvelope(JsonObject envelope) {
        requireInt(envelope, "schemaVersion",
                OutputClosureContract.SCHEMA_VERSION);
        requireText(envelope, "kind", OutputClosureContract.KIND);
        JsonObject scope = requireObject(envelope, "producer");
        OutputClosureContract.Producer producer =
                new OutputClosureContract.Producer(
                        requireText(scope, "relationKey"),
                        requireText(scope, "regionId"),
                        declaredOutputPorts(scope));

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
        return new OutputClosureContract(producer, members);
    }

    /**
     * Combines already decoded contracts. Exact duplicates collapse; observed
     * versions of one port become alternate captures plus an alignment gap.
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
                    "cannot merge different producer relations");
            } else {
                // Each contract publishes only the declarations its own
                // members rely on, so the merged relation needs their union
                // or a merged member would be refused by a declaration that
                // travelled with a different contract.
                producer = producer.withDeclaredOutputPorts(
                        contract.producer().declaredOutputPorts());
            }
            for (OutputClosureContract.Member member : contract.members()) {
                OutputClosureContract.Member prior =
                        members.putIfAbsent(member.portId(), member);
                if (prior != null) {
                    members.put(member.portId(), mergeMember(prior,
                            member));
                }
            }
        }
        return new OutputClosureContract(producer, members.values());
    }

    /** Retains exactly the output members selected by target-first demand. */
    public static OutputClosureContract project(
            OutputClosureContract contract, Collection<String> outputPorts) {
        if (contract == null || outputPorts == null
                || outputPorts.isEmpty()) {
            throw new IllegalArgumentException(
                    "output closure projection requires selected outputs");
        }
        Set<String> requested = new TreeSet<>();
        for (String output : outputPorts) {
            String port = output == null ? "" : output.trim();
            if (port.isEmpty() || !requested.add(port)) {
                throw new IllegalArgumentException(
                        "output closure projection has blank or duplicate "
                                + "output: " + output);
            }
        }
        List<OutputClosureContract.Member> selected = new ArrayList<>();
        for (String port : requested) {
            OutputClosureContract.Member member = contract.member(port);
            if (member == null) {
                throw new IllegalArgumentException(
                        "selected output is absent from closure: " + port);
            }
            selected.add(member);
        }
        return new OutputClosureContract(contract.producer(), selected);
    }

    private static OutputClosureContract.Member mergeMember(
            OutputClosureContract.Member left,
            OutputClosureContract.Member right) {
        JsonObject first = left.toJson();
        JsonObject second = right.toJson();
        JsonObject firstOutput = first.getAsJsonObject("output");
        JsonObject secondOutput = second.getAsJsonObject("output");
        for (String field : Arrays.asList("outputSiteId",
                "outputOccurrence", "replayOccurrence")) {
            firstOutput.remove(field);
            secondOutput.remove(field);
        }
        if (!firstOutput.equals(secondOutput)) {
            throw new IllegalArgumentException(
                    "conflicting output member " + left.portId());
        }
        JsonObject firstSlice = first.getAsJsonObject("slice");
        JsonObject secondSlice = second.getAsJsonObject("slice");
        TreeSet<String> changed = new TreeSet<>();
        for (String field : SCOPE_ARRAYS) {
            mergeStringArray(firstSlice, secondSlice, field);
        }
        mergeStringArray(firstSlice, secondSlice, "captureBindingIssues");
        mergeCaptureBindings(firstSlice, secondSlice);
        for (String field : Arrays.asList("activationLocalOccurrence",
                "selectedRuntimeEventSeq", "captureAnchorPort",
                "selectedFieldReceiverObjectId", "branchReplay")) {
            JsonElement a = firstSlice.remove(field);
            JsonElement b = secondSlice.remove(field);
            if (a == null ? b != null : !a.equals(b)) changed.add(field);
        }
        for (String field : differingFields(firstSlice, secondSlice)) {
            if (!"alignmentGaps".equals(field)) changed.add(field);
        }
        if (!changed.isEmpty()) {
            JsonArray gaps = firstSlice.has("alignmentGaps")
                    ? firstSlice.getAsJsonArray("alignmentGaps")
                    : new JsonArray();
            JsonObject gap = new JsonObject();
            gap.addProperty("kind", "OUTPUT_VERSION_ALIGNMENT_GAP");
            gap.addProperty("reason", "observed output versions use "
                    + "different replay details");
            JsonArray fields = new JsonArray();
            for (String field : changed) fields.add(field);
            gap.add("fields", fields);
            gaps.add(gap);
            firstSlice.add("alignmentGaps", gaps);
        }
        return decodeMember(first, 0);
    }

    private static void mergeStringArray(JsonObject target,
                                         JsonObject source, String field) {
        TreeSet<String> values = new TreeSet<>();
        for (JsonElement value : requireArray(target, field)) {
            values.add(value.getAsString());
        }
        for (JsonElement value : requireArray(source, field)) {
            values.add(value.getAsString());
        }
        JsonArray merged = new JsonArray();
        for (String value : values) merged.add(value);
        target.add(field, merged);
        source.add(field, merged.deepCopy());
    }

    private static void mergeCaptureBindings(JsonObject target,
                                             JsonObject source) {
        Map<String, JsonObject> bindings = new LinkedHashMap<>();
        for (JsonArray rows : Arrays.asList(
                requireArray(target, "captureBindings"),
                requireArray(source, "captureBindings"))) {
            for (JsonElement element : rows) {
                JsonObject binding = element.getAsJsonObject().deepCopy();
                binding.remove("captureBindingId");
                String key = CanonicalJson.render(binding);
                binding.addProperty("captureBindingId", "CAPTURE."
                        + UUID.nameUUIDFromBytes(key.getBytes(
                        StandardCharsets.UTF_8)));
                bindings.putIfAbsent(key, binding);
            }
        }
        JsonArray merged = new JsonArray();
        for (JsonObject binding : bindings.values()) merged.add(binding);
        target.add("captureBindings", merged);
        source.add("captureBindings", merged.deepCopy());
    }

    private static Set<String> differingFields(JsonObject left,
                                                JsonObject right) {
        TreeSet<String> result = new TreeSet<>();
        TreeSet<String> fields = new TreeSet<>(left.keySet());
        fields.addAll(right.keySet());
        for (String field : fields) {
            JsonElement a = left.get(field);
            JsonElement b = right.get(field);
            if (a == null ? b != null : !a.equals(b)) result.add(field);
        }
        return result;
    }

    /**
     * Builds one canonical member at the planner boundary.  This is the only
     * supported adapter for producers that still hold their frozen slice as a
     * separate value; it never creates or decodes singular activation mirrors.
     */
    public static OutputClosureContract singleton(
            String relationKey, String regionId,
            String portId, String cell, String kind,
            String javaType, JsonObject slice) {
        return singleton(relationKey, regionId,
                Collections.<String>emptyList(), portId, cell, kind,
                javaType, slice);
    }

    /**
     * The same adapter for a producer whose region declares output ports its
     * own region identity does not mint - a communication cut is the case.
     *
     * <p>{@code declaredOutputPorts} is the region's own declaration, passed
     * through unfiltered: the contract admits exactly the ids in it and
     * refuses everything else by name, so a port nothing declared can never
     * become a closure member.</p>
     */
    public static OutputClosureContract singleton(
            String relationKey, String regionId,
            Collection<String> declaredOutputPorts,
            String portId, String cell, String kind,
            String javaType, JsonObject slice) {
        JsonObject normalizedSlice = slice == null
                ? null : slice.deepCopy();
        JsonArray captures = requireArray(normalizedSlice,
                "captureBindings");
        if (normalizedSlice.has("causalEdges")) {
            throw new IllegalArgumentException(
                    "slice must reference external edges by causalEdgeIds");
        }
        String descriptor = javaTypeDescriptor(javaType);
        requireFieldDescriptor(descriptor, "requested output");

        JsonObject output = new JsonObject();
        output.addProperty("portId", portId);
        output.addProperty("cell", cell);
        output.addProperty("kind", kind);
        output.addProperty("javaTypeDescriptor", descriptor);
        if (captures.size() > 0
                && hasOutputOccurrenceIdentity(
                captures.get(0).getAsJsonObject())) {
            JsonObject capture = captures.get(0).getAsJsonObject();
            output.addProperty("outputSiteId",
                    requireText(capture, "outputSiteId"));
            output.addProperty("outputOccurrence", requireIntAtLeast(
                    capture, "outputOccurrence", 1));
            output.addProperty("replayOccurrence", requireIntAtLeast(
                    capture, "replayOccurrence", 1));
        }
        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", normalizedSlice);

        OutputClosureContract.Producer producer =
                new OutputClosureContract.Producer(relationKey, regionId,
                        declaredOutputPorts);
        OutputClosureContract.Member decoded = decodeMember(member, 0);
        producer.requireOutputPort(decoded.portId());
        return new OutputClosureContract(producer,
                Collections.singletonList(decoded));
    }

    public static void writeTo(JsonObject activation,
                               OutputClosureContract contract) {
        if (activation == null || contract == null) {
            throw new IllegalArgumentException(
                    "activation and output closure are required");
        }
        validateOuterScope(activation, contract.producer());
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
        validateOutputOccurrenceIdentity(output, bindings, path);
        return new OutputClosureContract.Member(output, slice);
    }

    /**
     * If the reusable output endpoint itself declares one occurrence, every
     * capture must agree. A merged best-effort member omits that declaration
     * and lets each capture retain its own observed occurrence.
     */
    private static void validateOutputOccurrenceIdentity(
            JsonObject output, JsonArray bindings, String path) {
        if (!hasOutputOccurrenceIdentity(output)) return;

        String siteId = requireText(output, "outputSiteId");
        int occurrence = requireIntAtLeast(output,
                "outputOccurrence", 1);
        int replay = requireIntAtLeast(output,
                "replayOccurrence", 1);
        // The ordinal is recorded provenance, not a replay demand: only its
        // internal coherence with the capture ledger is validated here.
        if (occurrence != replay) {
            throw new IllegalArgumentException(path
                    + " output occurrence is outside the bounded replay");
        }
        for (JsonElement element : bindings) {
            JsonObject capture = element.getAsJsonObject();
            if (!siteId.equals(requireText(capture, "outputSiteId"))
                    || occurrence != requireIntAtLeast(capture,
                    "outputOccurrence", 1)
                    || replay != requireIntAtLeast(capture,
                    "replayOccurrence", 1)) {
                throw new IllegalArgumentException(path
                        + " capture output occurrence identity mismatch");
            }
        }
    }

    private static boolean hasOutputOccurrenceIdentity(JsonObject value) {
        return value.has("outputSiteId")
                || value.has("outputOccurrence")
                || value.has("replayOccurrence");
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
            String captureKind = text(binding, "captureKind");
            if (OutputCaptureSpec.CALL_ARGUMENT.equals(captureKind)) {
                validateCallArgumentEndpoint(binding, path, descriptor);
            } else if (OutputCaptureSpec.COMMUNICATION_EFFECT.equals(
                    captureKind)) {
                validateCommunicationEffectEndpoint(binding, cell, path,
                        descriptor);
            } else if (OutputCaptureSpec.MUTATION_STATE.equals(
                    captureKind)) {
                validateMutationStateEndpoint(binding, cell, path,
                        descriptor);
            } else if (OutputCaptureSpec.FIELD_WRITE_STATE.equals(
                    captureKind)) {
                validateFieldWriteStateEndpoint(binding, cell, path,
                        descriptor);
            } else if (OutputCaptureSpec.HANDOFF_BOUND_LEAF.equals(
                    captureKind)) {
                validateHandoffBoundLeafEndpoint(binding, port, cell, path,
                        descriptor);
            } else if (OutputCaptureSpec.REGION_EXIT_FIELD.equals(
                    captureKind)) {
                if (hasOutputOccurrenceIdentity(binding)) {
                    throw new IllegalArgumentException(path
                            + " bounded heap outputs require an exact-site "
                            + "captureKind");
                }
                validateExitFieldEndpoint(binding, cell, path, descriptor);
            } else {
                throw new IllegalArgumentException(path
                        + " captureKind is unsupported: " + captureKind);
            }
        }
    }

    /**
     * Validates a structured leaf at the broker boundary.
     *
     * <p>No positional or name-only recovery is accepted here.  The capture
     * names the declared parent and encoding authority plus the exact
     * static site and direction.  The expression and its dynamic delivery
     * identity come directly from the VM handoff and its {@code VALUE_HANDOFF}
     * ledger edge; this reusable output declaration does not re-attest an
     * exchange, attempt, or runtime edge.</p>
     */
    private static void validateHandoffBoundLeafEndpoint(
            JsonObject binding, String port, String cell, String path,
            String descriptor) {
        String javaType = requireText(binding, "javaType");
        String parent = requireText(binding,
                CommunicationCatalogContract.PORT_COMPONENT_OF);
        String authority = requireText(binding,
                CommunicationCatalogContract.PORT_ENCODING_AUTHORITY);
        String site = requireText(binding,
                CommunicationCatalogContract.EXCHANGE_SITE_KEY);
        String leaf = requireText(binding, "leafPath");
        String direction = requireText(binding,
                CommunicationCatalogContract.PORT_DIRECTION);
        String terminal = leaf.substring(leaf.lastIndexOf('/') + 1);
        String expectedLeg = CommunicationCatalogContract.DIRECTION_REQUEST
                .equals(direction) ? ".req." : ".resp";
        boolean declaredDirection = CommunicationCatalogContract.DIRECTION_REQUEST.equals(direction)
                || CommunicationCatalogContract.DIRECTION_RESPONSE.equals(
                direction);
        if (!cell.equals(port)
                || !descriptor.equals(javaTypeDescriptor(javaType))
                || parent.equals(port)
                || !parent.startsWith(site + expectedLeg)
                || !port.startsWith(site + expectedLeg)
                || authority.isEmpty() || !declaredDirection
                || !port.endsWith("." + terminal)
                || binding.has("argumentIndex")
                || binding.has("declaredCallee")) {
            throw new IllegalArgumentException(path
                    + " handoff-bound leaf is inconsistent");
        }
    }

    private static void validateCallArgumentEndpoint(
            JsonObject binding, String path, String descriptor) {
        String javaType = requireText(binding, "javaType");
        if (!descriptor.equals(javaTypeDescriptor(javaType))
                || requireIntAtLeast(binding, "definitionUnitIndex", 0) < 0
                || requireIntAtLeast(binding, "argumentIndex", 0) < 0) {
            throw new IllegalArgumentException(
                    path + " call-argument capture is inconsistent");
        }
        requireText(binding, "definitionMethod");
        requireText(binding, "declaredCallee");
    }

    private static void validateCommunicationEffectEndpoint(
            JsonObject binding, String cell, String path,
            String descriptor) {
        if (!hasOutputOccurrenceIdentity(binding)) {
            throw new IllegalArgumentException(path
                    + " communication effect has no bounded occurrence");
        }
        String method = requireText(binding, "definitionMethod");
        String javaType = requireText(binding, "javaType");
        if (!descriptor.equals(javaTypeDescriptor(javaType))
                || !cell.equals(method + ".communication.response")
                || binding.has("argumentIndex")
                || binding.has("declaredCallee")) {
            throw new IllegalArgumentException(
                    path + " communication effect is inconsistent");
        }
    }

    private static void validateMutationStateEndpoint(
            JsonObject binding, String cell, String path,
            String descriptor) {
        validateExactHeapEndpoint(binding, cell, path, descriptor);
        requireText(binding, "declaredCallee");
    }

    private static void validateFieldWriteStateEndpoint(
            JsonObject binding, String cell, String path,
            String descriptor) {
        validateExactHeapEndpoint(binding, cell, path, descriptor);
    }

    private static void validateExactHeapEndpoint(
            JsonObject binding, String cell, String path,
            String descriptor) {
        if (!hasOutputOccurrenceIdentity(binding)) {
            throw new IllegalArgumentException(path
                    + " exact heap capture has no bounded occurrence");
        }
        DeclaredField field = FieldPathSpec.declaredField(
                requireText(binding, "fieldSignature"));
        String javaType = requireText(binding, "javaType");
        if (field == null || !cell.equals(field.signature())
                || !field.type().equals(javaType)
                || !descriptor.equals(javaTypeDescriptor(javaType))) {
            throw new IllegalArgumentException(path
                    + " exact heap capture is inconsistent");
        }
        requireText(binding, "definitionMethod");
        requireIntAtLeast(binding, "definitionUnitIndex", 0);
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

    /**
     * The producer's declared output ports, as the wire states them.
     *
     * <p>Absent means "this producer declares nothing outside its own
     * region", which is the shape every artifact written before cut ports
     * existed has.  Present means the region named these ports, so the
     * encoding is held to exactly the canonical form
     * {@link OutputClosureContract.Producer#toJson()} writes back: a
     * non-empty array of ids none of which the region identity already
     * mints.  An empty array or a re-declared region-scoped id would decode
     * to something the producer does not re-encode, and a wire that does not
     * round-trip is not a contract.</p>
     */
    private static List<String> declaredOutputPorts(JsonObject scope) {
        String field = OutputClosureContract.Producer.DECLARED_OUTPUT_PORTS;
        if (!scope.has(field)) return Collections.emptyList();
        Set<String> declared = stringSet(scope, field);
        if (declared.isEmpty()) {
            throw new IllegalArgumentException(
                    field + " must not be empty when present");
        }
        String prefix = requireText(scope, "regionId") + ".out.";
        for (String port : declared) {
            if (port.startsWith(prefix) && port.length() > prefix.length()) {
                throw new IllegalArgumentException(
                        field + " must not restate a region-scoped port: "
                                + port);
            }
        }
        return new ArrayList<>(declared);
    }

    private static void requireFieldDescriptor(String value, String path) {
        if (!validFieldDescriptor(value)) {
            throw new IllegalArgumentException(
                    path + ".javaTypeDescriptor is invalid: " + value);
        }
    }

    private static int requireIntAtLeast(
            JsonObject object, String name, int minimum) {
        JsonElement value = object == null ? null : object.get(name);
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isNumber()) {
            throw new IllegalArgumentException(name + " must be an integer");
        }
        int result;
        try {
            result = value.getAsInt();
        } catch (RuntimeException malformed) {
            throw new IllegalArgumentException(name + " must be an integer",
                    malformed);
        }
        if (result < minimum) {
            throw new IllegalArgumentException(name + " must be >= "
                    + minimum);
        }
        return result;
    }

    private static void validateOuterScope(
            JsonObject activation, OutputClosureContract.Producer producer) {
        if ((activation.has("regionId")
                && !producer.regionId().equals(
                requireText(activation, "regionId")))
                || (activation.has("relationKey")
                && !producer.relationKey().equals(
                requireText(activation, "relationKey")))) {
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
