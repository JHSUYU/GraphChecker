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

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.required;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.trimmed;

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

    public Member member(String portId) { return byPort.get(trimmed(portId)); }

    public SortedSet<String> outputPorts() {
        return Collections.unmodifiableSortedSet(
                new TreeSet<>(byPort.keySet()));
    }

    /**
     * Ports produced only by instance-scoped once-only heap writes.
     *
     * <p>Such a write's recorded version is an instance-level fact (see
     * {@link OutputCaptureSpec#INSTANCE_SCOPED_PRODUCER}), so a complete
     * occurrence of a {@code LOOP_BODY_ROOT} region that did not sample the
     * once-entered write still owes no per-occurrence production of this port.
     * Empty for every closure that has no such capture, so callers gated on it
     * are inert wherever the once-only-root rule never fired.</p>
     */
    public SortedSet<String> instanceScopedOutputPorts() {
        SortedSet<String> ports = new TreeSet<>();
        for (Member member : members) {
            JsonArray captures = member.captures();
            if (captures.size() == 0) continue;
            boolean all = true;
            for (JsonElement element : captures) {
                if (!element.isJsonObject()
                        || !element.getAsJsonObject().has(
                                OutputCaptureSpec.INSTANCE_SCOPED_PRODUCER)
                        || !element.getAsJsonObject().get(
                                OutputCaptureSpec.INSTANCE_SCOPED_PRODUCER)
                                .getAsBoolean()) {
                    all = false;
                    break;
                }
            }
            if (all) ports.add(member.portId());
        }
        return Collections.unmodifiableSortedSet(ports);
    }

    /**
     * The subset of {@link #instanceScopedOutputPorts()} whose whole demanded
     * writer set resolves to an explicit instance-scoped once-only heap
     * write.
     *
     * <p>Fail-closed in every direction: a port with no capture binding, a
     * binding that will not decode, a spec that does not state the flag, or a
     * spec that states it on a capture kind that is not an exact heap write
     * is simply absent, so a caller gated on this set keeps whatever demand it
     * states today.  Only a port whose entire writer set states the flag on a
     * heap write is named -- one non-instance-scoped writer means some
     * occurrence does owe this port.</p>
     */
    public SortedSet<String> onceOnlyInstanceScopedPorts() {
        SortedSet<String> named = instanceScopedOutputPorts();
        SortedSet<String> ports = new TreeSet<>();
        for (Member member : members) {
            if (!named.contains(member.portId())) continue;
            JsonArray captures = member.captures();
            if (captures.size() == 0) continue;
            boolean all = true;
            for (JsonElement element : captures) {
                OutputCaptureSpec spec;
                try {
                    spec = OutputCaptureSpec.decodeValidated(
                            element.getAsJsonObject());
                } catch (RuntimeException unresolvable) {
                    all = false;
                    break;
                }
                if (!spec.instanceScopedProducer()
                        || !spec.capturesExactHeapWrite()) {
                    all = false;
                    break;
                }
            }
            if (all) ports.add(member.portId());
        }
        return Collections.unmodifiableSortedSet(ports);
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

    public static final class Producer {
        /** Output ports the producing region declared by name, beyond those
         *  its region identity mints; absent when it declares none. */
        public static final String DECLARED_OUTPUT_PORTS =
                "declaredOutputPorts";

        private final String relationKey;
        private final String regionId;
        private final SortedSet<String> declaredOutputPorts;

        Producer(String relationKey, String regionId,
                 Collection<String> declaredOutputPorts) {
            this.relationKey = required(relationKey,
                    "producer.relationKey");
            this.regionId = required(regionId, "producer.regionId");
            TreeSet<String> declared = new TreeSet<>();
            for (String port : declaredOutputPorts == null
                    ? Collections.<String>emptyList()
                    : declaredOutputPorts) {
                String id = trimmed(port);
                // A region-scoped port is already admitted by the region
                // identity it is minted from, so re-declaring it says
                // nothing.
                if (id.isEmpty() || regionScoped(id)) continue;
                declared.add(id);
            }
            this.declaredOutputPorts =
                    Collections.unmodifiableSortedSet(declared);
        }

        public String relationKey() { return relationKey; }

        public String regionId() { return regionId; }

        /** The non-region-scoped output ports the producer's region declared.
         *  Static discovery names a cut port after the exchange site, so the
         *  region identity cannot decide whether it is its own; this can. */
        public SortedSet<String> declaredOutputPorts() {
            return declaredOutputPorts;
        }

        /** Relation identity only: a declaration is a static fact about the
         *  region, and a contract may come from a wire with no cut port. */
        boolean sameAs(Producer other) {
            return other != null
                    && relationKey.equals(other.relationKey)
                    && regionId.equals(other.regionId);
        }

        Producer withDeclaredOutputPorts(Collection<String> ports) {
            TreeSet<String> union = new TreeSet<>(declaredOutputPorts);
            if (ports != null) {
                for (String port : ports) {
                    String id = trimmed(port);
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

        /** A member port is admitted when the region minted it or declared
         *  it by name; membership is exact, never a prefix or a shape. */
        void requireOutputPort(String portId) {
            String id = trimmed(portId);
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
}
