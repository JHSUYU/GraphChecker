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
import java.util.TreeMap;
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
    public static final int SCHEMA_VERSION = 2;
    public static final String KIND = "OUTPUT_CLOSURE_CONTRACT";

    private final Producer producer;
    private final List<Member> members;
    private final List<JsonObject> causalEdges;
    private final Map<String, Member> byPort;
    private final ExecutionScope executionScope;
    private final String demandKey;
    private final String closureFingerprint;

    OutputClosureContract(Producer producer, Collection<Member> source,
                          Collection<JsonObject> edgeSource) {
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
        TreeMap<String, JsonObject> edgeIndex = new TreeMap<>();
        if (edgeSource != null) {
            for (JsonObject edge : edgeSource) {
                String id = text(edge, "edgeId");
                JsonObject prior = edgeIndex.putIfAbsent(id,
                        edge.deepCopy());
                if (id.isEmpty() || prior != null
                        && !CanonicalJson.render(prior).equals(
                        CanonicalJson.render(edge))) {
                    throw new IllegalArgumentException(
                            "duplicate, conflicting or missing causal edge");
                }
            }
        }
        this.producer = producer;
        this.members = Collections.unmodifiableList(ordered);
        this.causalEdges = Collections.unmodifiableList(
                new ArrayList<>(edgeIndex.values()));
        this.byPort = Collections.unmodifiableMap(index);
        this.executionScope = new ExecutionScope(ordered);
        if (!edgeIndex.keySet().containsAll(
                this.executionScope.causalEdgeIds())) {
            throw new IllegalArgumentException(
                    "output closure cites a missing causal edge");
        }
        this.demandKey = CanonicalJson.sha256(demandIdentity());
        this.closureFingerprint = CanonicalJson.sha256(toJson());
    }

    public Producer producer() { return producer; }

    public List<Member> members() { return members; }

    public List<JsonObject> causalEdges() {
        List<JsonObject> result = new ArrayList<>();
        for (JsonObject edge : causalEdges) result.add(edge.deepCopy());
        return Collections.unmodifiableList(result);
    }

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
        JsonArray edges = new JsonArray();
        for (JsonObject edge : causalEdges) edges.add(edge.deepCopy());
        result.add("causalEdges", edges);
        JsonArray encoded = new JsonArray();
        for (Member member : members) encoded.add(member.toJson());
        result.add("members", encoded);
        return result;
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

        /**
         * The exact program site this port is published at, empty when the
         * port names none.  The encoded identity is
         * {@code KIND:<method>#u<n>...}; only that leading unit position is a
         * control-flow location, the rest names the argument, callee or field
         * the capture reads there.
         */
        public String outputSite() {
            String encoded = text(output, "outputSiteId");
            int start = encoded.indexOf('<');
            int marker = start < 0 ? -1 : encoded.indexOf(">#u", start);
            if (marker < 0) return "";
            int end = marker + 3;
            while (end < encoded.length()
                    && Character.isDigit(encoded.charAt(end))) {
                end++;
            }
            return end == marker + 3 ? ""
                    : encoded.substring(start, end);
        }

        public JsonObject slice() { return slice.deepCopy(); }

        public JsonArray captures() { return captureBindings().deepCopy(); }

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
        private final SortedSet<String> outputSites;

        private ExecutionScope(List<Member> members) {
            inputs = union(members, "inputPorts");
            sites = union(members, "sites");
            staticSites = union(members, "staticSites");
            methods = union(members, "methods");
            edges = union(members, "causalEdgeIds");
            TreeSet<String> published = new TreeSet<>();
            for (Member member : members) {
                String site = member.outputSite();
                if (!site.isEmpty()) published.add(site);
            }
            outputSites = Collections.unmodifiableSortedSet(published);
        }

        public SortedSet<String> inputPorts() { return inputs; }

        public SortedSet<String> branchSites() {
            TreeSet<String> result = new TreeSet<>(sites);
            result.addAll(staticSites);
            return Collections.unmodifiableSortedSet(result);
        }

        public SortedSet<String> staticSites() { return staticSites; }

        /** Unit positions the demanded outputs are published at. */
        public SortedSet<String> outputSites() { return outputSites; }

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
