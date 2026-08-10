package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;

/**
 * Configured scalar values observed at logical protocol call boundaries.
 *
 * <p>The declaration is intentionally independent of the transport
 * implementation and of Soot.  The runtime recorder and the offline static
 * analysis therefore read exactly the same mapping rows.  A path contains
 * canonical declared-field signatures and the literal {@code []} for each
 * reference-array descent.  Only scalar leaves are admitted; object carriers
 * never become implicit value equalities.</p>
 */
public final class ProtocolBoundaryScalarConfig {
    public static final String ARRAY_ELEMENT = "[]";
    public static final String VALUE_AUTHORITY =
            "EXACT_CONFIGURED_RPC_BOUNDARY_SCALAR_V1";
    public static final String GAP_AUTHORITY =
            "CONFIGURED_RPC_BOUNDARY_SCALAR_GAP_V1";

    private final Map<String, Mapping> byClient;
    private final Map<String, Mapping> byServer;
    private final Map<String, List<Leaf>> leavesByMapping;
    private final ConcurrentMap<String, ClientResolution> clientResolutions =
            new ConcurrentHashMap<>();

    private ProtocolBoundaryScalarConfig(Map<String, Mapping> byClient,
                                         Map<String, Mapping> byServer,
                                         Map<String, List<Leaf>> leaves) {
        this.byClient = byClient;
        this.byServer = byServer;
        this.leavesByMapping = leaves;
    }

    /** Reads {@code causynth.protocol.stubs}/its environment equivalent. */
    public static ProtocolBoundaryScalarConfig fromConfiguration()
            throws IOException {
        String configured = firstNonBlank(
                System.getProperty("causynth.protocol.stubs"),
                System.getenv("CAUSYNTH_PROTOCOL_STUBS"));
        return configured == null ? empty()
                : read(Paths.get(configured).toAbsolutePath().normalize());
    }

    /** Reads and validates boundary declarations without resolving methods. */
    public static ProtocolBoundaryScalarConfig read(Path path)
            throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            throw new IOException("Protocol stub mapping not found: " + path);
        }
        Map<String, Mapping> clients = new LinkedHashMap<>();
        Map<String, Mapping> servers = new LinkedHashMap<>();
        Map<String, List<Leaf>> leaves = new LinkedHashMap<>();
        Map<String, Mapping> mappings = new LinkedHashMap<>();
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            int lineNumber = 0;
            while ((line = reader.readLine()) != null) {
                lineNumber++;
                if (line.trim().isEmpty()) continue;
                try {
                    JsonElement parsed = JsonParser.parseString(line);
                    if (!parsed.isJsonObject()) {
                        throw new IllegalArgumentException(
                                "mapping must be a JSON object");
                    }
                    parseMapping(parsed.getAsJsonObject(), clients, servers,
                            leaves, mappings);
                } catch (RuntimeException invalid) {
                    throw new IOException("Invalid protocol boundary scalar "
                            + "mapping at " + path + ":" + lineNumber + ": "
                            + invalid.getMessage(), invalid);
                }
            }
        }
        return new ProtocolBoundaryScalarConfig(clients, servers, leaves);
    }

    /** Leaves observed at one client call argument or return boundary. */
    public List<Leaf> clientLeaves(String method, String direction,
                                   int argumentIndex) {
        return leaves(clientMapping(trim(method)), "CLIENT", direction,
                argumentIndex);
    }

    private Mapping clientMapping(String method) {
        ClientResolution resolution = clientResolutions.get(method);
        if (resolution == null) {
            ClientResolution computed = resolveClient(method);
            ClientResolution prior = clientResolutions.putIfAbsent(method,
                    computed);
            resolution = prior == null ? computed : prior;
        }
        if (resolution.ambiguity != null) {
            throw new IllegalArgumentException(resolution.ambiguity);
        }
        return resolution.mapping;
    }

    private ClientResolution resolveClient(String method) {
        MethodSignature actual = MethodSignature.parse(method);
        Mapping exact = byClient.get(method);
        List<String> matchedMethods = new ArrayList<>();
        List<Mapping> matchedMappings = new ArrayList<>();
        if (exact != null) {
            matchedMethods.add(method);
            matchedMappings.add(exact);
        }
        if (actual != null) {
            Class<?> actualOwner = runtimeClass(actual.owner, null);
            if (actualOwner != null) {
                for (Map.Entry<String, Mapping> entry
                        : byClient.entrySet()) {
                    if (method.equals(entry.getKey())) continue;
                    MethodSignature configured = MethodSignature.parse(
                            entry.getKey());
                    if (configured == null || !actual.subSignature.equals(
                            configured.subSignature)) {
                        continue;
                    }
                    Class<?> configuredOwner = runtimeClass(
                            configured.owner, actualOwner.getClassLoader());
                    if (configuredOwner != null
                            && configuredOwner.isAssignableFrom(actualOwner)) {
                        matchedMethods.add(entry.getKey());
                        matchedMappings.add(entry.getValue());
                    }
                }
            }
        }
        if (matchedMappings.size() > 1) {
            return ClientResolution.ambiguous("ambiguous clientStub "
                    + "implementation: " + method + " matches "
                    + matchedMethods);
        }
        return matchedMappings.isEmpty() ? ClientResolution.NONE
                : ClientResolution.match(matchedMappings.get(0));
    }

    private static Class<?> runtimeClass(String name,
                                         ClassLoader preferred) {
        Set<ClassLoader> loaders = new LinkedHashSet<>();
        if (preferred != null) loaders.add(preferred);
        try {
            ClassLoader context = Thread.currentThread()
                    .getContextClassLoader();
            if (context != null) loaders.add(context);
        } catch (SecurityException ignored) {
            // The defining loader below remains a deterministic fallback.
        }
        ClassLoader defining = ProtocolBoundaryScalarConfig.class
                .getClassLoader();
        if (defining != null) loaders.add(defining);
        try {
            ClassLoader system = ClassLoader.getSystemClassLoader();
            if (system != null) loaders.add(system);
        } catch (SecurityException ignored) {
            // A restricted runtime may still resolve through earlier loaders.
        }
        for (ClassLoader loader : loaders) {
            try {
                return Class.forName(name, false, loader);
            } catch (ClassNotFoundException | LinkageError
                     | SecurityException ignored) {
                // Try the next loader and cache a negative result if none do.
            }
        }
        return null;
    }

    /** Leaves observed at one server method argument or return boundary. */
    public List<Leaf> serverLeaves(String method, String direction,
                                   int argumentIndex) {
        return leaves(byServer.get(trim(method)), "SERVER", direction,
                argumentIndex);
    }

    public List<Leaf> mappingLeaves(String mappingId) {
        return leavesByMapping.getOrDefault(trim(mappingId),
                Collections.<Leaf>emptyList());
    }

    private List<Leaf> leaves(Mapping mapping, String side,
                              String direction, int argumentIndex) {
        if (mapping == null) return Collections.emptyList();
        List<Leaf> result = new ArrayList<>();
        for (Leaf leaf : leavesByMapping.getOrDefault(mapping.id,
                Collections.<Leaf>emptyList())) {
            if (!leaf.direction.equals(trim(direction))) continue;
            if ("RESPONSE".equals(leaf.direction)
                    || leaf.argumentIndex(side) == argumentIndex) {
                result.add(leaf);
            }
        }
        return Collections.unmodifiableList(result);
    }

    private static void parseMapping(
            JsonObject row, Map<String, Mapping> clients,
            Map<String, Mapping> servers, Map<String, List<Leaf>> leaves,
            Map<String, Mapping> mappings) {
        String client = required(row, "clientStub");
        String server = required(row, "serverStub");
        if (row.has("carrierProjection")) {
            throw new IllegalArgumentException("carrierProjection is retired; "
                    + "declare boundaryScalarLeaves instead");
        }
        JsonElement declared = row.get("boundaryScalarLeaves");
        if (declared != null && !declared.isJsonNull()
                && !declared.isJsonArray()) {
            throw new IllegalArgumentException(
                    "boundaryScalarLeaves must be an array");
        }
        boolean hasDeclaredLeaves = declared != null
                && !declared.isJsonNull()
                && declared.getAsJsonArray().size() > 0;
        String explicitId = string(row, "id");
        if (hasDeclaredLeaves && explicitId.isEmpty()) {
            throw new IllegalArgumentException("boundaryScalarLeaves require "
                    + "an explicit stable protocol mapping id");
        }
        String id = explicitId.isEmpty()
                ? client + " -> " + server : explicitId;
        Mapping mapping = new Mapping(id, requestPorts(row.get("request")),
                bool(row, "response"));
        if (mappings.putIfAbsent(id, mapping) != null) {
            throw new IllegalArgumentException(
                    "duplicate protocol mapping id: " + id);
        }

        if (declared == null || declared.isJsonNull()) return;
        if (integer(row, "schemaVersion", -1) != 2) {
            throw new IllegalArgumentException("boundaryScalarLeaves require "
                    + "protocol mapping schemaVersion exactly 2");
        }
        if (!"PROTOCOL_STUB_MAPPING".equals(string(row, "kind"))) {
            throw new IllegalArgumentException("boundaryScalarLeaves require "
                    + "kind PROTOCOL_STUB_MAPPING");
        }
        if (declared.getAsJsonArray().size() == 0) return;
        Set<String> leafIds = new LinkedHashSet<>();
        Set<String> semanticPaths = new LinkedHashSet<>();
        List<Leaf> parsedLeaves = leaves.computeIfAbsent(id,
                ignored -> new ArrayList<Leaf>());
        for (JsonElement element : declared.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "boundary scalar leaf must be an object");
            }
            Leaf leaf = parseLeaf(mapping, element.getAsJsonObject());
            if (!leafIds.add(leaf.leafId())) {
                throw new IllegalArgumentException(
                        "duplicate boundary scalar leaf id: "
                                + leaf.leafId());
            }
            if (!semanticPaths.add(leaf.semanticPathIdentity())) {
                throw new IllegalArgumentException("duplicate boundary "
                        + "scalar semantic path: "
                        + leaf.semanticPathIdentity());
            }
            parsedLeaves.add(leaf);
        }
        // Rows without demanded leaves remain the static protocol catalog's
        // concern.  In particular, its supported context conflict diagnostics
        // must not be shadowed by this independent runtime-boundary catalog.
        putUnique(clients, client, mapping, "clientStub");
        putUnique(servers, server, mapping, "serverStub");
    }

    private static Leaf parseLeaf(Mapping mapping, JsonObject row) {
        String id = required(row, "leafId");
        String direction = required(row, "direction").toUpperCase();
        if (!"REQUEST".equals(direction) && !"RESPONSE".equals(direction)) {
            throw new IllegalArgumentException(
                    "boundary scalar direction must be REQUEST or RESPONSE");
        }
        String port = string(row, "port");
        int clientArgument = -1;
        int serverParameter = -1;
        if ("REQUEST".equals(direction)) {
            RequestPort request = mapping.request.get(port);
            if (request == null) {
                throw new IllegalArgumentException(
                        "request boundary scalar names unknown port: " + port);
            }
            clientArgument = request.clientArgument;
            serverParameter = request.serverParameter;
        } else {
            if (!mapping.response) {
                throw new IllegalArgumentException(
                        "response boundary scalar requires mapped response");
            }
            if (port.isEmpty()) port = "response";
            if (!"response".equals(port)) {
                throw new IllegalArgumentException(
                        "response boundary scalar port must be response");
            }
        }

        List<String> path = strings(row, "declaredPath");
        if (path.isEmpty()) {
            throw new IllegalArgumentException(
                    "boundary scalar declaredPath must be non-empty");
        }
        int arraySteps = 0;
        String priorType = "";
        FieldPathSpec.DeclaredField leaf = null;
        for (String step : path) {
            if (ARRAY_ELEMENT.equals(step)) {
                if (!arrayType(priorType)) {
                    throw new IllegalArgumentException(
                            "[] must follow a declared array field");
                }
                priorType = arrayComponent(priorType);
                arraySteps++;
                leaf = null;
                continue;
            }
            FieldPathSpec.DeclaredField field =
                    FieldPathSpec.declaredField(step);
            if (field == null) {
                throw new IllegalArgumentException(
                        "invalid declared field in boundary path: " + step);
            }
            priorType = field.type();
            leaf = field;
        }
        if (leaf == null || !scalarType(leaf.type())) {
            throw new IllegalArgumentException(
                    "boundary path must end at a scalar declared field");
        }
        int bound = integer(row, "containerBound", -1);
        if (arraySteps == 0 && bound >= 0) {
            throw new IllegalArgumentException(
                    "containerBound requires an [] path step");
        }
        if (arraySteps > 0 && (bound < 1 || bound
                > LoopBoundPolicy.SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY)) {
            throw new IllegalArgumentException("containerBound must be 1.."
                    + LoopBoundPolicy.SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY);
        }
        return new Leaf(mapping.id, id, direction, port, path,
                leaf.type(), clientArgument, serverParameter,
                arraySteps == 0 ? 0 : bound);
    }

    private static Map<String, RequestPort> requestPorts(JsonElement value) {
        Map<String, RequestPort> result = new LinkedHashMap<>();
        if (value == null || value.isJsonNull()) return result;
        if (value.isJsonPrimitive()
                && "POSITIONAL".equals(value.getAsString())) {
            // Positional arity is resolved by ConfiguredProtocolStubs.  A
            // boundary declaration that needs one of these arguments uses
            // the explicit object form so its name and both indices remain
            // reviewable in configuration.
            return result;
        }
        if (!value.isJsonArray()) {
            throw new IllegalArgumentException(
                    "request must be POSITIONAL or an array");
        }
        for (JsonElement element : value.getAsJsonArray()) {
            JsonObject port = element.getAsJsonObject();
            String name = required(port, "name");
            RequestPort request = new RequestPort(
                    integer(port, "clientArgument", -1),
                    integer(port, "serverParameter", -1));
            if (request.clientArgument < 0 || request.serverParameter < 0
                    || result.put(name, request) != null) {
                throw new IllegalArgumentException(
                        "invalid or duplicate request port: " + name);
            }
        }
        return result;
    }

    private static void putUnique(Map<String, Mapping> target, String key,
                                  Mapping mapping, String role) {
        Mapping prior = target.putIfAbsent(key, mapping);
        if (prior != null && !prior.id.equals(mapping.id)) {
            throw new IllegalArgumentException("ambiguous " + role + ": "
                    + key);
        }
    }

    private static ProtocolBoundaryScalarConfig empty() {
        return new ProtocolBoundaryScalarConfig(new LinkedHashMap<>(),
                new LinkedHashMap<>(), new LinkedHashMap<>());
    }

    private static boolean scalarType(String value) {
        String type = trim(value);
        return "boolean".equals(type) || "byte".equals(type)
                || "char".equals(type) || "short".equals(type)
                || "int".equals(type) || "long".equals(type)
                || "float".equals(type) || "double".equals(type)
                || "java.lang.String".equals(type);
    }

    private static boolean arrayType(String value) {
        String type = trim(value);
        return type.startsWith("[") || type.endsWith("[]");
    }

    private static String arrayComponent(String value) {
        String type = trim(value);
        if (type.endsWith("[]")) {
            return type.substring(0, type.length() - 2);
        }
        if (type.startsWith("[L") && type.endsWith(";")) {
            return type.substring(2, type.length() - 1).replace('/', '.');
        }
        if (type.startsWith("[[")) return type.substring(1);
        return "";
    }

    private static List<String> strings(JsonObject row, String field) {
        JsonElement value = row.get(field);
        if (value == null || !value.isJsonArray()) {
            return Collections.emptyList();
        }
        List<String> result = new ArrayList<>();
        for (JsonElement element : value.getAsJsonArray()) {
            if (!element.isJsonPrimitive() || trim(element.getAsString())
                    .isEmpty()) {
                throw new IllegalArgumentException(field
                        + " must contain non-empty strings");
            }
            result.add(trim(element.getAsString()));
        }
        return Collections.unmodifiableList(result);
    }

    private static String required(JsonObject row, String field) {
        String value = string(row, field);
        if (value.isEmpty()) {
            throw new IllegalArgumentException(field + " is required");
        }
        return value;
    }

    private static String string(JsonObject row, String field) {
        JsonElement value = row.get(field);
        return value == null || value.isJsonNull() ? ""
                : trim(value.getAsString());
    }

    private static boolean bool(JsonObject row, String field) {
        JsonElement value = row.get(field);
        return value != null && !value.isJsonNull()
                && value.getAsBoolean();
    }

    private static int integer(JsonObject row, String field, int fallback) {
        JsonElement value = row.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException invalid) {
            return fallback;
        }
    }

    private static String firstNonBlank(String... values) {
        for (String value : values) {
            if (!trim(value).isEmpty()) return trim(value);
        }
        return null;
    }

    private static String trim(String value) {
        return value == null ? "" : value.trim();
    }

    private static final class Mapping {
        private final String id;
        private final Map<String, RequestPort> request;
        private final boolean response;

        private Mapping(String id, Map<String, RequestPort> request,
                        boolean response) {
            this.id = id;
            this.request = request;
            this.response = response;
        }
    }

    private static final class ClientResolution {
        private static final ClientResolution NONE =
                new ClientResolution(null, null);

        private final Mapping mapping;
        private final String ambiguity;

        private ClientResolution(Mapping mapping, String ambiguity) {
            this.mapping = mapping;
            this.ambiguity = ambiguity;
        }

        private static ClientResolution match(Mapping mapping) {
            return new ClientResolution(mapping, null);
        }

        private static ClientResolution ambiguous(String message) {
            return new ClientResolution(null, message);
        }
    }

    private static final class MethodSignature {
        private final String owner;
        private final String subSignature;

        private MethodSignature(String owner, String subSignature) {
            this.owner = owner;
            this.subSignature = subSignature;
        }

        private static MethodSignature parse(String method) {
            String value = trim(method);
            if (!value.startsWith("<") || !value.endsWith(">")) {
                return null;
            }
            int separator = value.indexOf(':', 1);
            if (separator < 2 || separator >= value.length() - 2) {
                return null;
            }
            String owner = trim(value.substring(1, separator));
            String subSignature = trim(value.substring(separator + 1,
                    value.length() - 1));
            int firstSpace = subSignature.indexOf(' ');
            int open = subSignature.indexOf('(', firstSpace + 1);
            int close = subSignature.lastIndexOf(')');
            if (owner.isEmpty() || firstSpace < 1
                    || open <= firstSpace + 1
                    || close != subSignature.length() - 1) {
                return null;
            }
            return new MethodSignature(owner, subSignature);
        }
    }

    private static final class RequestPort {
        private final int clientArgument;
        private final int serverParameter;

        private RequestPort(int clientArgument, int serverParameter) {
            this.clientArgument = clientArgument;
            this.serverParameter = serverParameter;
        }
    }

    /** One validated scalar leaf declaration. */
    public static final class Leaf {
        private final String mappingId;
        private final String leafId;
        private final String direction;
        private final String port;
        private final List<String> declaredPath;
        private final String javaType;
        private final int clientArgument;
        private final int serverParameter;
        private final int containerBound;

        private Leaf(String mappingId, String leafId, String direction,
                     String port, List<String> declaredPath, String javaType,
                     int clientArgument, int serverParameter,
                     int containerBound) {
            this.mappingId = mappingId;
            this.leafId = leafId;
            this.direction = direction;
            this.port = port;
            this.declaredPath = Collections.unmodifiableList(
                    new ArrayList<>(declaredPath));
            this.javaType = javaType;
            this.clientArgument = clientArgument;
            this.serverParameter = serverParameter;
            this.containerBound = containerBound;
        }

        public String mappingId() { return mappingId; }
        public String leafId() { return leafId; }
        public String direction() { return direction; }
        public String port() { return port; }
        public List<String> declaredPath() { return declaredPath; }
        public String javaType() { return javaType; }
        public int containerBound() { return containerBound; }

        public int argumentIndex(String side) {
            return "CLIENT".equals(trim(side))
                    ? clientArgument : serverParameter;
        }

        private String semanticPathIdentity() {
            return direction + "\n" + port + "\n" + declaredPath;
        }
    }
}
