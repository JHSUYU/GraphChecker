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

/** Immutable output contract shared by every occurrence of one relation. */
public final class OutputClosureContract {
    public static final String FIELD = "outputClosure";
    public static final int SCHEMA_VERSION = 3;
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

    private JsonObject demandIdentity() {
        JsonObject result = producer.toJson();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
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
        /**
         * Output ports the producing region declared by name, beyond the ones
         * its own region identity mints.
         *
         * <p>Absent for a producer that publishes nothing outside its own
         * region, so such a producer's wire form is exactly what it was
         * before this member existed.</p>
         */
        public static final String DECLARED_OUTPUT_PORTS =
                "declaredOutputPorts";

        private final String relationKey;
        private final String regionId;
        private final SortedSet<String> declaredOutputPorts;

        Producer(String relationKey, String regionId) {
            this(relationKey, regionId, Collections.<String>emptyList());
        }

        Producer(String relationKey, String regionId,
                 Collection<String> declaredOutputPorts) {
            this.relationKey = required(relationKey,
                    "producer.relationKey");
            this.regionId = required(regionId, "producer.regionId");
            TreeSet<String> declared = new TreeSet<>();
            for (String port : declaredOutputPorts == null
                    ? Collections.<String>emptyList()
                    : declaredOutputPorts) {
                String id = trim(port);
                // A region-scoped port is already admitted by the region
                // identity it is minted from, so re-declaring it says
                // nothing.  Dropping it here is what keeps a producer that
                // declares only region-scoped outputs byte-identical to the
                // form it had before declarations existed.
                if (id.isEmpty() || regionScoped(id)) continue;
                declared.add(id);
            }
            this.declaredOutputPorts =
                    Collections.unmodifiableSortedSet(declared);
        }

        public String relationKey() { return relationKey; }

        public String regionId() { return regionId; }

        /**
         * The non-region-scoped output ports this producer's region declared.
         *
         * <p>A communication cut is the case that needs this: static
         * discovery names a cut port after the exchange site it belongs to
         * ({@code <exchangeSiteKey>.req.<name>}, {@code .resp},
         * {@code .live.<carrier>}), not after the region, so the region
         * identity cannot decide whether such a port is one of its own.  The
         * declaration can, and it admits exactly the declared ids.</p>
         */
        public SortedSet<String> declaredOutputPorts() {
            return declaredOutputPorts;
        }

        /**
         * Relation identity only.  A declaration is a static fact about the
         * region, not a distinguishing part of the relation: two contracts of
         * one relation cannot legitimately disagree about it, and one of them
         * may simply have been decoded from a wire that carried no cut port.
         */
        boolean sameAs(Producer other) {
            return other != null
                    && relationKey.equals(other.relationKey)
                    && regionId.equals(other.regionId);
        }

        Producer withDeclaredOutputPorts(Collection<String> ports) {
            TreeSet<String> union = new TreeSet<>(declaredOutputPorts);
            if (ports != null) {
                for (String port : ports) {
                    String id = trim(port);
                    if (!id.isEmpty() && !regionScoped(id)) union.add(id);
                }
            }
            return union.equals(declaredOutputPorts) ? this
                    : new Producer(relationKey, regionId, union);
        }

        private boolean regionScoped(String portId) {
            String prefix = regionId + ".out.";
            return portId.startsWith(prefix)
                    && portId.length() > prefix.length();
        }

        /**
         * A member port is admitted when the region minted it
         * ({@code <regionId>.out.<id>}) or when the region declared it by
         * name.  Anything else is outside this producer and still throws:
         * membership is exact, never a prefix or a shape.
         */
        void requireOutputPort(String portId) {
            String id = trim(portId);
            if (regionScoped(id) || declaredOutputPorts.contains(id)) return;
            throw new IllegalArgumentException(
                    "output port is outside producer region: " + portId);
        }

        JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("relationKey", relationKey);
            result.addProperty("regionId", regionId);
            if (!declaredOutputPorts.isEmpty()) {
                JsonArray declared = new JsonArray();
                for (String port : declaredOutputPorts) declared.add(port);
                result.add(DECLARED_OUTPUT_PORTS, declared);
            }
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

        /** Static publication site, when the capture exposes one. */
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
