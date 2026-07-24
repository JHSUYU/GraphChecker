package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;

/**
 * Immutable wire value for one producer invocation and its demanded outputs.
 *
 * <p>This class preserves the complete slice payload.  It does not certify
 * dynamic materialization or capture: Scheduler and Importer remain the two
 * semantic trust boundaries for those proofs.</p>
 */
public final class OutputClosureContract {
    public static final String FIELD = "outputClosure";
    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "OUTPUT_CLOSURE_CONTRACT";

    private final Producer producer;
    private final List<Member> members;
    private final Map<String, Member> byPort;
    private final ExecutionScope executionScope;
    private final String demandKey;
    private final String closureFingerprint;

    OutputClosureContract(Producer producer, Collection<Member> source) {
        if (producer == null || source == null || source.isEmpty()) {
            throw new IllegalArgumentException(
                    "producer and at least one output member are required");
        }
        List<Member> ordered = new ArrayList<>(source);
        ordered.sort((left, right) ->
                left.portId().compareTo(right.portId()));
        Map<String, Member> index = new LinkedHashMap<>();
        TreeSet<String> captureIds = new TreeSet<>();
        for (Member member : ordered) {
            if (member == null) {
                throw new IllegalArgumentException(
                        "output closure member must not be null");
            }
            producer.requireOutputPort(member.portId());
            if (index.put(member.portId(), member) != null) {
                throw new IllegalArgumentException(
                        "duplicate output identity " + member.portId());
            }
            for (JsonElement row : member.captureBindings()) {
                String id = text(row.getAsJsonObject(), "captureBindingId");
                if (id.isEmpty() || !captureIds.add(id)) {
                    throw new IllegalArgumentException(
                            "duplicate or missing captureBindingId");
                }
            }
        }
        this.producer = producer;
        this.members = Collections.unmodifiableList(ordered);
        this.byPort = Collections.unmodifiableMap(index);
        this.executionScope = new ExecutionScope(ordered);
        this.demandKey = CanonicalJson.sha256(demandIdentity());
        this.closureFingerprint = CanonicalJson.sha256(toJson());
    }

    public Producer producer() { return producer; }

    public List<Member> members() { return members; }

    public Member member(String portId) { return byPort.get(trim(portId)); }

    public SortedSet<String> outputPorts() {
        return Collections.unmodifiableSortedSet(
                new TreeSet<>(byPort.keySet()));
    }

    public ExecutionScope executionScope() { return executionScope; }

    public String demandKey() { return demandKey; }

    public String closureFingerprint() { return closureFingerprint; }

    public JsonObject toJson() {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("kind", KIND);
        result.add("producer", producer.toJson());
        JsonArray encoded = new JsonArray();
        for (Member member : members) encoded.add(member.toJson());
        result.add("members", encoded);
        return result;
    }

    /** V1 joint execution is deliberately bounded to direct scalars. */
    public boolean supportedJointCapture() {
        if (members.size() == 1) return true;
        for (Member member : members) {
            if (member.javaTypeDescriptor().length() != 1
                    || !"ZBCSIJFD".contains(member.javaTypeDescriptor())
                    || !member.captureRequired()
                    || !member.captureComplete()
                    || member.captureBindings().size() != 1) {
                return false;
            }
            String kind = text(member.captureBindings().get(0)
                            .getAsJsonObject(),
                    "captureKind");
            if (!"CALL_ARGUMENT".equals(kind)
                    && !"FIELD_ASSIGNMENT_RHS".equals(kind)) {
                return false;
            }
        }
        return true;
    }

    private JsonObject demandIdentity() {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("producerRegionId", producer.regionId);
        JsonArray outputs = new JsonArray();
        for (Member member : members) {
            JsonObject output = new JsonObject();
            output.addProperty("portId", member.portId());
            output.addProperty("cell", member.cell());
            output.addProperty("kind", member.outputKind());
            output.addProperty("javaTypeDescriptor",
                    member.javaTypeDescriptor());
            outputs.add(output);
        }
        result.add("outputs", outputs);
        return result;
    }

    static String text(JsonObject value, String name) {
        JsonElement element = value == null ? null : value.get(name);
        return element != null && element.isJsonPrimitive()
                && element.getAsJsonPrimitive().isString()
                ? element.getAsString().trim() : "";
    }

    static String trim(String value) {
        return value == null ? "" : value.trim();
    }

    public static final class Producer {
        private final String regionId;
        private final String regionInstanceId;
        private final long rootCallId;

        Producer(String regionId, String regionInstanceId, long rootCallId) {
            this.regionId = required(regionId, "producer.regionId");
            this.regionInstanceId = required(regionInstanceId,
                    "producer.regionInstanceId");
            if (rootCallId < 0
                    || !this.regionInstanceId.startsWith(this.regionId + "@")
                    || !this.regionInstanceId.endsWith(
                    "#call" + rootCallId)) {
                throw new IllegalArgumentException(
                        "producer invocation scope is inconsistent");
            }
            this.rootCallId = rootCallId;
        }

        public String regionId() { return regionId; }

        public String regionInstanceId() { return regionInstanceId; }

        public long rootCallId() { return rootCallId; }

        boolean sameAs(Producer other) {
            return other != null && regionId.equals(other.regionId)
                    && regionInstanceId.equals(other.regionInstanceId)
                    && rootCallId == other.rootCallId;
        }

        void requireOutputPort(String portId) {
            String prefix = regionId + ".out.";
            if (!portId.startsWith(prefix)
                    || portId.length() == prefix.length()) {
                throw new IllegalArgumentException(
                        "output port is outside producer region: " + portId);
            }
        }

        JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("regionId", regionId);
            result.addProperty("regionInstanceId", regionInstanceId);
            result.addProperty("rootCallId", rootCallId);
            return result;
        }
    }

    public static final class Member {
        private final JsonObject output;
        private final JsonObject slice;

        Member(JsonObject output, JsonObject slice) {
            this.output = output.deepCopy();
            this.slice = slice.deepCopy();
        }

        public String portId() { return text(output, "portId"); }

        public String cell() { return text(output, "cell"); }

        public String outputKind() { return text(output, "kind"); }

        public String javaTypeDescriptor() {
            return text(output, "javaTypeDescriptor");
        }

        public boolean captureRequired() {
            return slice.get("captureBindingsRequired").getAsBoolean();
        }

        public boolean captureComplete() {
            return slice.get("captureBindingsComplete").getAsBoolean();
        }

        public JsonObject output() { return output.deepCopy(); }

        public JsonObject slice() { return slice.deepCopy(); }

        public JsonArray captures() { return captureBindings().deepCopy(); }

        JsonObject executionOutput() {
            JsonObject result = new JsonObject();
            result.addProperty("symbol", portId());
            result.addProperty("cell", cell());
            result.addProperty("kind", outputKind());
            result.addProperty("location",
                    "FAILURE_PREDICATE".equals(outputKind())
                            ? "THROW_OR_BRANCH"
                            : "RETURN_OR_HEAP_EFFECT");
            result.addProperty("javaTypeDescriptor",
                    javaTypeDescriptor());
            return result;
        }

        JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.add("output", output.deepCopy());
            result.add("slice", slice.deepCopy());
            return result;
        }

        private JsonArray captureBindings() {
            return slice.getAsJsonArray("captureBindings");
        }
    }

    public static final class ExecutionScope {
        private final SortedSet<String> inputs;
        private final SortedSet<String> sites;
        private final SortedSet<String> staticSites;
        private final SortedSet<String> methods;
        private final SortedSet<String> edges;

        private ExecutionScope(List<Member> members) {
            inputs = union(members, "inputPorts");
            sites = union(members, "sites");
            staticSites = union(members, "staticSites");
            methods = union(members, "methods");
            edges = union(members, "causalEdgeIds");
        }

        public SortedSet<String> inputPorts() { return inputs; }

        public SortedSet<String> sites() { return sites; }

        public SortedSet<String> staticSites() { return staticSites; }

        public SortedSet<String> branchSites() {
            TreeSet<String> result = new TreeSet<>(sites);
            result.addAll(staticSites);
            return Collections.unmodifiableSortedSet(result);
        }

        public SortedSet<String> methods() { return methods; }

        public SortedSet<String> causalEdgeIds() { return edges; }

        private static SortedSet<String> union(
                List<Member> members, String field) {
            TreeSet<String> result = new TreeSet<>();
            for (Member member : members) {
                for (JsonElement value
                        : member.slice.getAsJsonArray(field)) {
                    result.add(value.getAsString().trim());
                }
            }
            return Collections.unmodifiableSortedSet(result);
        }
    }

    private static String required(String value, String label) {
        String result = trim(value);
        if (result.isEmpty()) {
            throw new IllegalArgumentException(label + " is required");
        }
        return result;
    }
}
