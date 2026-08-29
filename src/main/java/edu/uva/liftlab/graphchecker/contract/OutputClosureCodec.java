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
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.exactInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.required;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.requiredArray;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.requiredObject;
import static edu.uva.liftlab.graphchecker.contract.OutputClosureContract.text;

/**
 * Versioned structural codec for {@link OutputClosureContract}.  It proves
 * wire shape, relation identity and direct endpoint consistency; dynamic
 * occurrence identity belongs to the causal skeleton.
 */
public final class OutputClosureCodec {
    /** Exactly the kinds a producer mints; see the three
     *  {@code OutputClosureCodec.singleton} call sites. */
    private static final Set<String> OUTPUT_KINDS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "REGION_OUTPUT", "HEAP_STATE", "INTERACTION_EVENT")));
    private static final List<String> SCOPE_ARRAYS = Arrays.asList(
            "inputPorts", "sites", "staticSites", "methods",
            "causalEdgeIds");
    private static final List<String> DYNAMIC_REPLAY_FIELDS = Arrays.asList(
            "activationLocalOccurrence", "selectedRuntimeEventSeq",
            "selectedRuntimeCallId", "captureAnchorPort",
            "captureAnchorSiteId",
            "selectedFieldReceiverObjectId",
            "definitionCompletionSeq", "lastMutationCompletionSeq",
            "observedDefinitionCallId", "foldedMutationCount",
            "foldedMutationCompletionSeqs", "concreteCallReturns");

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
        OutputClosureContract contract = decodeEnvelope(
                encoded.getAsJsonObject());
        validateOuterScope(artifact, contract.producer());
        return contract;
    }

    public static OutputClosureContract decodeEnvelope(JsonObject envelope) {
        if (exactInteger(envelope, "schemaVersion", -1)
                != OutputClosureContract.SCHEMA_VERSION
                || !OutputClosureContract.KIND.equals(
                        text(envelope, "kind"))) {
            throw new IllegalArgumentException(
                    "unsupported outputClosure envelope");
        }
        JsonObject scope = requiredObject(envelope, "producer");
        OutputClosureContract.Producer producer =
                new OutputClosureContract.Producer(
                        requiredText(scope, "relationKey"),
                        requiredText(scope, "regionId"),
                        declaredOutputPorts(scope));

        JsonArray rows = requiredArray(envelope, "members");
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

    /** Combines already decoded contracts.  Exact duplicates collapse;
     *  observed versions of one port become alternate captures plus a gap. */
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
                // members rely on, so the merge needs their union.
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

    /**
     * Projects folded heap writers to the exact version selected by their
     * outgoing runtime edge.  A producer with no selected outgoing edge for a
     * member keeps the union catalog.  One selected writer narrows to its
     * exact slice; several selected writers keep the bounded union because
     * they are distinct versions produced by the same coarse occurrence and
     * are captured together by its one replay task.
     */
    public static OutputClosureContract projectSelectedVersions(
            OutputClosureContract contract,
            Map<String, Set<String>> selectedOutgoingEdges) {
        if (contract == null || selectedOutgoingEdges == null) {
            throw new IllegalArgumentException(
                    "version projection requires a closure and edge map");
        }
        JsonObject encoded = contract.toJson();
        for (JsonElement element : encoded.getAsJsonArray("members")) {
            JsonObject member = element.getAsJsonObject();
            JsonObject output = member.getAsJsonObject("output");
            String port = requiredText(output, "portId");
            Set<String> selectedEdges = selectedOutgoingEdges.getOrDefault(
                    port, Collections.<String>emptySet());
            JsonObject slice = member.getAsJsonObject("slice");
            JsonArray versions = optionalArray(slice,
                    "boundedVersionScopes");
            if (versions.size() == 0 || selectedEdges.isEmpty()) continue;

            JsonObject selected = null;
            int selectedVersions = 0;
            Set<String> coveredEdges = new LinkedHashSet<>();
            for (JsonElement versionElement : versions) {
                if (!versionElement.isJsonObject()) continue;
                JsonObject version = versionElement.getAsJsonObject();
                Set<String> versionEdges = stringSet(version,
                        "causalEdgeIds");
                if (Collections.disjoint(versionEdges, selectedEdges)) {
                    continue;
                }
                selectedVersions++;
                selected = version;
                for (String edge : selectedEdges) {
                    if (versionEdges.contains(edge)) coveredEdges.add(edge);
                }
            }
            if (selected == null || !coveredEdges.equals(selectedEdges)) {
                throw new IllegalArgumentException("selected output edges have "
                        + "no bounded writer version: " + port + " -> "
                        + selectedEdges);
            }
            if (selectedVersions > 1) {
                // The folded member already is the one bounded capture
                // contract for all versions of this static output site.  Its
                // exact outgoing edge ledger still decides which captured
                // version reaches each downstream read.
                continue;
            }
            int occurrence = exactInteger(selected,
                    "outputOccurrence", -1);
            JsonObject exactSlice = selected.deepCopy();
            exactSlice.remove("outputOccurrence");
            exactSlice.remove("boundedVersionScopes");
            member.add("slice", exactSlice);
            if (occurrence > 0) {
                output.addProperty("outputOccurrence", occurrence);
                for (JsonElement captureElement
                        : requiredArray(exactSlice, "captureBindings")) {
                    JsonObject capture = captureElement.getAsJsonObject();
                    capture.addProperty("outputOccurrence", occurrence);
                }
            }
        }
        return decodeEnvelope(encoded);
    }

    private static OutputClosureContract.Member mergeMember(
            OutputClosureContract.Member left,
            OutputClosureContract.Member right) {
        JsonObject first = left.toJson();
        JsonObject second = right.toJson();
        if (first.equals(second)) {
            return decodeMember(first, 0);
        }
        TreeSet<String> changed = new TreeSet<>();
        JsonObject firstOutput = first.getAsJsonObject("output");
        JsonObject secondOutput = second.getAsJsonObject("output");
        for (String field : Arrays.asList("outputSiteId",
                "outputOccurrence")) {
            mergeReplayScalar(firstOutput, secondOutput, field, changed);
        }
        if (!firstOutput.equals(secondOutput)) {
            throw new IllegalArgumentException(
                    "conflicting output member " + left.portId());
        }
        JsonObject firstSlice = first.getAsJsonObject("slice");
        JsonObject secondSlice = second.getAsJsonObject("slice");
        for (String field : SCOPE_ARRAYS) {
            mergeStringArray(firstSlice, secondSlice, field, false);
        }
        mergeStringArray(firstSlice, secondSlice,
                "demandedHeapDeclarations", true);
        mergeStringArray(firstSlice, secondSlice, "captureBindingIssues",
                false);
        mergeCaptureBindings(firstSlice, secondSlice);
        mergeAlignmentGaps(firstSlice, secondSlice);
        for (String field : DYNAMIC_REPLAY_FIELDS) {
            mergeReplayScalar(firstSlice, secondSlice, field, changed);
        }
        for (String field : differingFields(firstSlice, secondSlice)) {
            if ("alignmentGaps".equals(field)) continue;
            throw new IllegalArgumentException(
                    "conflicting output slice field " + left.portId()
                            + ": " + field);
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
            firstSlice.add("alignmentGaps",
                    normalizeAlignmentGaps(gaps));
        }
        return decodeMember(first, 0);
    }

    /** Preserves an exact scalar boundary and drops only conflicting ones. */
    private static void mergeReplayScalar(
            JsonObject target, JsonObject source, String field,
            Set<String> changed) {
        JsonElement first = target.get(field);
        JsonElement second = source.get(field);
        if (first == null && second == null
                || first != null && first.equals(second)) {
            return;
        }
        target.remove(field);
        source.remove(field);
        changed.add(field);
    }

    /** Alignment gaps are monotone evidence across nested/order-reversed merges. */
    private static void mergeAlignmentGaps(
            JsonObject target, JsonObject source) {
        JsonArray gaps = new JsonArray();
        for (JsonElement element : optionalArray(target,
                "alignmentGaps")) {
            gaps.add(element.deepCopy());
        }
        for (JsonElement element : optionalArray(source,
                "alignmentGaps")) {
            gaps.add(element.deepCopy());
        }
        target.remove("alignmentGaps");
        source.remove("alignmentGaps");
        if (gaps.size() == 0) return;
        target.add("alignmentGaps", normalizeAlignmentGaps(gaps));
    }

    private static JsonArray normalizeAlignmentGaps(JsonArray values) {
        java.util.TreeMap<String, JsonElement> normalized =
                new java.util.TreeMap<>();
        java.util.TreeMap<String, JsonObject> versionGaps =
                new java.util.TreeMap<>();
        java.util.TreeMap<String, TreeSet<String>> versionFields =
                new java.util.TreeMap<>();
        for (JsonElement value : values) {
            if (!value.isJsonObject()
                    || !"OUTPUT_VERSION_ALIGNMENT_GAP".equals(
                    text(value.getAsJsonObject(), "kind"))) {
                normalized.put(CanonicalJson.render(value),
                        value.deepCopy());
                continue;
            }
            JsonObject gap = value.getAsJsonObject().deepCopy();
            JsonArray fields = optionalArray(gap, "fields");
            gap.remove("fields");
            String key = CanonicalJson.render(gap);
            versionGaps.putIfAbsent(key, gap);
            TreeSet<String> merged = versionFields.computeIfAbsent(key,
                    ignored -> new TreeSet<>());
            for (JsonElement field : fields) {
                if (!field.isJsonPrimitive()
                        || !field.getAsJsonPrimitive().isString()
                        || field.getAsString().trim().isEmpty()) {
                    throw new IllegalArgumentException(
                            "alignment gap fields must be strings");
                }
                merged.add(field.getAsString());
            }
        }
        for (Map.Entry<String, JsonObject> entry : versionGaps.entrySet()) {
            JsonObject gap = entry.getValue();
            JsonArray fields = new JsonArray();
            for (String field : versionFields.get(entry.getKey())) {
                fields.add(field);
            }
            gap.add("fields", fields);
            normalized.put(CanonicalJson.render(gap), gap);
        }
        JsonArray result = new JsonArray();
        for (JsonElement gap : normalized.values()) result.add(gap);
        return result;
    }

    /** Sorted union of one string member.  An {@code optional} member may be
     *  absent on both sides and is held to non-empty strings when present. */
    private static void mergeStringArray(JsonObject target, JsonObject source,
                                         String field, boolean optional) {
        if (optional && !target.has(field) && !source.has(field)) return;
        TreeSet<String> values = new TreeSet<>();
        for (JsonObject side : Arrays.asList(target, source)) {
            for (JsonElement value : optional ? optionalArray(side, field)
                    : requiredArray(side, field)) {
                if (optional && (!value.isJsonPrimitive()
                        || !value.getAsJsonPrimitive().isString()
                        || value.getAsString().trim().isEmpty())) {
                    throw new IllegalArgumentException(
                            field + " must contain non-empty strings");
                }
                values.add(value.getAsString());
            }
        }
        JsonArray merged = new JsonArray();
        for (String value : values) merged.add(value);
        target.add(field, merged);
        source.add(field, merged.deepCopy());
    }

    private static void mergeCaptureBindings(JsonObject target,
                                             JsonObject source) {
        Map<String, JsonObject> bindings = new java.util.TreeMap<>();
        for (JsonArray rows : Arrays.asList(
                requiredArray(target, "captureBindings"),
                requiredArray(source, "captureBindings"))) {
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

    /** One-member closure for a producer whose region declares output ports
     *  its own region identity does not mint - a communication cut is the
     *  case.  {@code declaredOutputPorts} passes through unfiltered: the
     *  contract admits exactly those ids and refuses everything else. */
    public static OutputClosureContract singleton(
            String relationKey, String regionId,
            Collection<String> declaredOutputPorts,
            String portId, String cell, String kind,
            String javaType, JsonObject slice) {
        JsonObject normalizedSlice = slice == null
                ? null : slice.deepCopy();
        JsonArray captures = requiredArray(normalizedSlice,
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
                    requiredText(capture, "outputSiteId"));
            output.addProperty("outputOccurrence", requireIntAtLeast(
                    capture, "outputOccurrence", 1));
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
        JsonObject output = requiredObject(encoded, "output");
        String port = requiredText(output, "portId");
        String cell = requiredText(output, "cell");
        String kind = requiredText(output, "kind");
        if (!OUTPUT_KINDS.contains(kind)) {
            throw new IllegalArgumentException(
                    path + ".output.kind is unsupported: " + kind);
        }
        String descriptor = requiredText(output, "javaTypeDescriptor");
        requireFieldDescriptor(descriptor, path);

        JsonObject slice = requiredObject(encoded, "slice");
        if (slice.has("causalEdges")) {
            throw new IllegalArgumentException(
                    path + ".slice contains non-canonical causalEdges");
        }
        validateSliceShape(slice, port, cell, path + ".slice");
        JsonArray bindings = requiredArray(slice, "captureBindings");
        validateCaptureLedger(bindings, port, cell, path,
                descriptor);
        validateOutputOccurrenceIdentity(output, bindings, path);
        return new OutputClosureContract.Member(output, slice);
    }

    /** If the reusable output endpoint declares one occurrence every capture
     *  must agree; a merged best-effort member omits the declaration. */
    private static void validateOutputOccurrenceIdentity(
            JsonObject output, JsonArray bindings, String path) {
        if (!hasOutputOccurrenceIdentity(output)) return;

        String siteId = requiredText(output, "outputSiteId");
        int occurrence = requireIntAtLeast(output,
                "outputOccurrence", 1);
        for (JsonElement element : bindings) {
            JsonObject capture = element.getAsJsonObject();
            if (!siteId.equals(requiredText(capture, "outputSiteId"))
                    || occurrence != requireIntAtLeast(capture,
                    "outputOccurrence", 1)) {
                throw new IllegalArgumentException(path
                        + " capture output occurrence identity mismatch");
            }
        }
    }

    private static boolean hasOutputOccurrenceIdentity(JsonObject value) {
        return value.has("outputSiteId")
                || value.has("outputOccurrence");
    }

    private static void validateSliceShape(
            JsonObject slice, String port, String cell, String path) {
        if (!port.equals(requiredText(slice, "outputPort"))
                || !cell.equals(requiredText(slice, "outputCell"))) {
            throw new IllegalArgumentException(
                    path + " output identity mismatch");
        }
        for (String name : SCOPE_ARRAYS) stringSet(slice, name);
        requiredArray(slice, "captureBindings");
        requiredArray(slice, "captureBindingIssues");
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
            if (!port.equals(requiredText(binding, "outputPort"))
                    || !cell.equals(requiredText(binding, "outputCell"))
                    || !ids.add(requiredText(binding, "captureBindingId"))) {
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
            } else if (OutputCaptureSpec.MUTATION_STATE.equals(captureKind)
                    || OutputCaptureSpec.FIELD_WRITE_STATE.equals(
                            captureKind)) {
                validateExactHeapEndpoint(binding, cell, path, descriptor);
                if (OutputCaptureSpec.MUTATION_STATE.equals(captureKind)) {
                    requiredText(binding, "declaredCallee");
                }
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

    /** Validates a structured leaf at the broker boundary.  No positional or
     *  name-only recovery is accepted: the capture names the declared parent,
     *  encoding authority, exact static site and direction; the expression and
     *  its delivery identity come from the VM handoff's VALUE_HANDOFF edge. */
    private static void validateHandoffBoundLeafEndpoint(
            JsonObject binding, String port, String cell, String path,
            String descriptor) {
        String javaType = requiredText(binding, "javaType");
        String parent = requiredText(binding,
                CommunicationCatalogContract.PORT_COMPONENT_OF);
        String authority = requiredText(binding,
                CommunicationCatalogContract.PORT_ENCODING_AUTHORITY);
        String site = requiredText(binding,
                CommunicationCatalogContract.EXCHANGE_SITE_KEY);
        String leaf = requiredText(binding, "leafPath");
        String direction = requiredText(binding,
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
        String javaType = requiredText(binding, "javaType");
        if (!descriptor.equals(javaTypeDescriptor(javaType))
                || requireIntAtLeast(binding, "definitionUnitIndex", 0) < 0
                || requireIntAtLeast(binding, "argumentIndex", 0) < 0) {
            throw new IllegalArgumentException(
                    path + " call-argument capture is inconsistent");
        }
        requiredText(binding, "definitionMethod");
        requiredText(binding, "declaredCallee");
    }

    private static void validateCommunicationEffectEndpoint(
            JsonObject binding, String cell, String path,
            String descriptor) {
        if (!hasOutputOccurrenceIdentity(binding)) {
            throw new IllegalArgumentException(path
                    + " communication effect has no bounded occurrence");
        }
        String method = requiredText(binding, "definitionMethod");
        String javaType = requiredText(binding, "javaType");
        if (!descriptor.equals(javaTypeDescriptor(javaType))
                || !cell.equals(method + ".communication.response")
                || binding.has("argumentIndex")
                || binding.has("declaredCallee")) {
            throw new IllegalArgumentException(
                    path + " communication effect is inconsistent");
        }
    }

    private static void validateExactHeapEndpoint(
            JsonObject binding, String cell, String path,
            String descriptor) {
        if (!hasOutputOccurrenceIdentity(binding)) {
            throw new IllegalArgumentException(path
                    + " exact heap capture has no bounded occurrence");
        }
        DeclaredField field = FieldPathSpec.declaredField(
                requiredText(binding, "fieldSignature"));
        String javaType = requiredText(binding, "javaType");
        if (field == null || !cell.equals(field.signature())
                || !field.type().equals(javaType)
                || !descriptor.equals(javaTypeDescriptor(javaType))) {
            throw new IllegalArgumentException(path
                    + " exact heap capture is inconsistent");
        }
        requiredText(binding, "definitionMethod");
        requireIntAtLeast(binding, "definitionUnitIndex", 0);
    }

    private static void validateExitFieldEndpoint(
            JsonObject binding, String cell, String path,
            String descriptor) {
        DeclaredField field = FieldPathSpec.declaredField(
                requiredText(binding, "fieldSignature"));
        List<String> fieldPath = FieldPathSpec.stringArray(binding,
                "fieldPath");
        String javaType = requiredText(binding, "javaType");
        if (field == null || !cell.equals(
                requiredText(binding, "fieldSignature"))
                || fieldPath.size() != 1
                || !field.name().equals(fieldPath.get(0))
                || !field.type().equals(javaType)
                || !descriptor.equals(javaTypeDescriptor(javaType))) {
            throw new IllegalArgumentException(
                    path + " region-exit field capture is inconsistent");
        }
        requiredText(binding, "accessRootInputPort");
    }

    /** The producer's declared output ports, as the wire states them.  Absent
     *  means the producer declares nothing outside its own region; present is
     *  held to the canonical form
     *  {@link OutputClosureContract.Producer#toJson()} writes back. */
    private static List<String> declaredOutputPorts(JsonObject scope) {
        String field = OutputClosureContract.Producer.DECLARED_OUTPUT_PORTS;
        if (!scope.has(field)) return Collections.emptyList();
        Set<String> declared = stringSet(scope, field);
        if (declared.isEmpty()) {
            throw new IllegalArgumentException(
                    field + " must not be empty when present");
        }
        String prefix = requiredText(scope, "regionId") + ".out.";
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
                requiredText(activation, "regionId")))
                || (activation.has("relationKey")
                && !producer.relationKey().equals(
                requiredText(activation, "relationKey")))) {
            throw new IllegalArgumentException(
                    "outputClosure producer conflicts with artifact scope");
        }
    }

    private static Set<String> stringSet(JsonObject object, String name) {
        Set<String> result = new LinkedHashSet<>();
        JsonArray values = requiredArray(object, name);
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

    private static JsonArray optionalArray(JsonObject object, String name) {
        JsonElement value = object == null ? null : object.get(name);
        if (value == null) return new JsonArray();
        if (!value.isJsonArray()) {
            throw new IllegalArgumentException(name + " must be an array");
        }
        return value.getAsJsonArray();
    }

    private static String requiredText(JsonObject object, String name) {
        return required(text(object, name), name);
    }
}
