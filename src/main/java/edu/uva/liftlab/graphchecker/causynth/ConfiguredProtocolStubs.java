package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import soot.ArrayType;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.VoidType;

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
import static edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.firstNonBlank;

/** Explicit protocol-layer call bridges. */
final class ConfiguredProtocolStubs {
    private final Map<String, List<ProtocolStubMapping>> byClient;
    private final Map<String, List<ProtocolStubMapping>> byServer;
    private final Set<String> clientOwners;
    private final List<ProtocolStubMapping> mappings;

    private ConfiguredProtocolStubs(
            Map<String, List<ProtocolStubMapping>> byClient,
            Map<String, List<ProtocolStubMapping>> byServer,
            Set<String> clientOwners,
            List<ProtocolStubMapping> mappings) {
        this.byClient = byClient;
        this.byServer = byServer;
        this.clientOwners = clientOwners;
        this.mappings = mappings;
    }

    static ConfiguredProtocolStubs fromConfiguration(
            Map<String, SootMethod> methods) throws IOException {
        String configured = firstNonBlank(
                System.getProperty("causynth.protocol.stubs"),
                System.getenv("CAUSYNTH_PROTOCOL_STUBS"));
        if (configured == null) {
            return empty();
        }
        Path path = Paths.get(configured).toAbsolutePath().normalize();
        if (!Files.isRegularFile(path)) {
            throw new IOException("Protocol stub mapping not found: " + path);
        }
        Map<String, List<ProtocolStubMapping>> byClient =
                new LinkedHashMap<>();
        Map<String, List<ProtocolStubMapping>> byServer =
                new LinkedHashMap<>();
        Set<String> clientOwners = new LinkedHashSet<>();
        List<ProtocolStubMapping> mappings = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            int lineNumber = 0;
            while ((line = reader.readLine()) != null) {
                lineNumber++;
                String trimmed = line.trim();
                if (trimmed.isEmpty()) {
                    continue;
                }
                ProtocolStubMapping mapping;
                try {
                    JsonElement parsed = JsonParser.parseString(trimmed);
                    if (!parsed.isJsonObject()) {
                        throw new IllegalArgumentException(
                                "mapping must be a JSON object");
                    }
                    mapping = parse(parsed.getAsJsonObject(), methods);
                } catch (RuntimeException malformed) {
                    throw new IOException("Invalid protocol stub mapping at "
                            + path + ":" + lineNumber + ": "
                            + malformed.getMessage(), malformed);
                }
                byClient.computeIfAbsent(mapping.clientStub,
                        ignored -> new ArrayList<>()).add(mapping);
                byServer.computeIfAbsent(mapping.serverStub,
                        ignored -> new ArrayList<>()).add(mapping);
                clientOwners.add(mapping.clientOwner);
                mappings.add(mapping);
            }
        }
        return new ConfiguredProtocolStubs(byClient, byServer, clientOwners,
                Collections.unmodifiableList(mappings));
    }

    List<ProtocolStubMapping> targets(String clientStub) {
        return byClient.getOrDefault(clientStub, Collections.emptyList());
    }

    List<ProtocolStubMapping> sources(String serverStub) {
        return byServer.getOrDefault(serverStub, Collections.emptyList());
    }

    List<ProtocolStubMapping> mappings() {
        return mappings;
    }

    boolean isClientOwner(String owner) {
        return clientOwners.contains(owner);
    }

    static ConfiguredProtocolStubs empty() {
        return new ConfiguredProtocolStubs(new LinkedHashMap<>(),
                new LinkedHashMap<>(), new LinkedHashSet<>(),
                Collections.emptyList());
    }

    private static ProtocolStubMapping parse(JsonObject row,
                                             Map<String, SootMethod> methods) {
        if (!row.has("schemaVersion")
                || row.get("schemaVersion").getAsInt() != 2
                || !"PROTOCOL_STUB_MAPPING".equals(string(row, "kind"))) {
            throw new IllegalArgumentException("protocol mapping requires "
                    + "schemaVersion 2 and kind PROTOCOL_STUB_MAPPING");
        }
        String id = string(row, "id");
        if (id.isEmpty()) {
            throw new IllegalArgumentException("protocol mapping requires "
                    + "an explicit stable id");
        }
        String clientStub = string(row, "clientStub");
        String serverStub = string(row, "serverStub");
        SootMethod client = methods.get(clientStub);
        SootMethod server = methods.get(serverStub);
        if (client == null || server == null || !server.isConcrete()) {
            throw new IllegalArgumentException(
                    "client/server stub method did not resolve: "
                            + clientStub + " -> " + serverStub);
        }

        List<ProtocolPortMapping> request = new ArrayList<>();
        JsonElement requestElement = row.get("request");
        if (requestElement != null && requestElement.isJsonPrimitive()
                && "POSITIONAL".equals(requestElement.getAsString())) {
            if (client.getParameterCount() != server.getParameterCount()) {
                throw new IllegalArgumentException(
                        "positional request arity differs");
            }
            for (int index = 0; index < client.getParameterCount(); index++) {
                request.add(port("arg" + index, index, index,
                        client, server));
            }
        } else if (requestElement != null && requestElement.isJsonArray()) {
            JsonArray ports = requestElement.getAsJsonArray();
            for (JsonElement element : ports) {
                JsonObject port = element.getAsJsonObject();
                request.add(port(string(port, "name"),
                        port.get("clientArgument").getAsInt(),
                        port.get("serverParameter").getAsInt(),
                        client, server));
            }
        }

        boolean response = row.has("response")
                && row.get("response").getAsBoolean();
        if (response && (client.getReturnType() instanceof VoidType
                || server.getReturnType() instanceof VoidType
                || !client.getReturnType().equals(server.getReturnType()))) {
            throw new IllegalArgumentException(
                    "mapped response types differ");
        }
        List<ResponseComponentMapping> responseComponents =
                responseComponents(row, response, client.getReturnType(),
                        methods);
        return new ProtocolStubMapping(id, string(row, "transport"),
                clientStub, serverStub, client.getDeclaringClass().getName(),
                request, response, responseComponents);
    }

    /**
     * Validates configured response accessors once and lowers them to exact
     * field declarations.
     */
    private static List<ResponseComponentMapping> responseComponents(
            JsonObject row, boolean response, Type responseType,
            Map<String, SootMethod> methods) {
        JsonElement encoded = row.get("responseComponents");
        if (encoded == null || encoded.isJsonNull()) {
            return Collections.emptyList();
        }
        if (!response || !encoded.isJsonArray()) {
            throw new IllegalArgumentException(
                    "responseComponents require a declared response");
        }
        List<ResponseComponentMapping> result = new ArrayList<>();
        Set<String> names = new LinkedHashSet<>();
        Set<List<String>> paths = new LinkedHashSet<>();
        for (JsonElement element : encoded.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "response component must be an object");
            }
            JsonObject component = element.getAsJsonObject();
            String name = string(component, "name");
            JsonElement pathElement = component.get("path");
            if (name.isEmpty() || name.indexOf('.') >= 0
                    || name.indexOf('/') >= 0 || pathElement == null
                    || !pathElement.isJsonArray()
                    || pathElement.getAsJsonArray().size() == 0) {
                throw new IllegalArgumentException(
                        "response component requires a stable name and path");
            }
            Type current = responseType;
            List<ResponsePathStep> path = new ArrayList<>();
            for (JsonElement stepElement : pathElement.getAsJsonArray()) {
                if (!stepElement.isJsonObject()) {
                    throw new IllegalArgumentException(
                            "response component path step must be an object");
                }
                JsonObject step = stepElement.getAsJsonObject();
                String getter = string(step, "getter");
                String fieldSignature = string(step, "field");
                String arrayElementType = string(step,
                        "uniqueArrayElementType");
                int choices = (getter.isEmpty() ? 0 : 1)
                        + (fieldSignature.isEmpty() ? 0 : 1)
                        + (arrayElementType.isEmpty() ? 0 : 1);
                if (choices != 1) {
                    throw new IllegalArgumentException(
                            "response path step requires exactly one field, "
                                    + "getter, or uniqueArrayElementType");
                }
                if (!arrayElementType.isEmpty()) {
                    if (!(current instanceof ArrayType)) {
                        throw new IllegalArgumentException(
                                "response array element selector follows a "
                                        + "non-array type: " + current);
                    }
                    SootClass selected = Scene.v().getSootClassUnsafe(
                            arrayElementType);
                    Type declaredElement =
                            ((ArrayType) current).getElementType();
                    if (selected == null || !compatibleArrayElement(
                            declaredElement, selected)) {
                        throw new IllegalArgumentException(
                                "response array element type is incompatible: "
                                        + arrayElementType + " in " + current);
                    }
                    path.add(ResponsePathStep.uniqueArrayElement(
                            arrayElementType));
                    current = selected.getType();
                    continue;
                }
                SootField field;
                if (!getter.isEmpty()) {
                    SootMethod method = methods.get(getter);
                    field = StructuralFieldAccessorProof.exactField(method);
                    if (field == null || !compatibleOwner(current,
                            method.getDeclaringClass())) {
                        throw new IllegalArgumentException(
                                "response getter is not one structural field "
                                        + "access: " + getter);
                    }
                } else {
                    field = exactField(fieldSignature);
                    if (field == null) {
                        throw new IllegalArgumentException(
                                "response field did not resolve exactly: "
                                        + fieldSignature);
                    }
                }
                if (!compatibleOwner(current,
                        field.getDeclaringClass())) {
                    throw new IllegalArgumentException(
                            "response field path owner/type mismatch: "
                                    + field.getSignature());
                }
                path.add(ResponsePathStep.field(field.getSignature()));
                current = field.getType();
            }
            ResponsePathStep terminal = path.get(path.size() - 1);
            FieldPathSpec.DeclaredField leaf = FieldPathSpec.declaredField(
                    terminal.declaration);
            if (current instanceof VoidType || leaf == null
                    || !name.equals(leaf.name())) {
                throw new IllegalArgumentException(
                        "response component must name its exact terminal "
                                + "leaf: " + name);
            }
            List<String> identity = new ArrayList<>();
            for (ResponsePathStep step : path) identity.add(step.identity());
            if (!names.add(name) || !paths.add(identity)) {
                throw new IllegalArgumentException(
                        "response component names and paths must be unique: "
                                + name);
            }
            result.add(new ResponseComponentMapping(name,
                    current.toString(), path));
        }
        return Collections.unmodifiableList(result);
    }

    private static boolean compatibleOwner(Type current, SootClass owner) {
        return current instanceof RefType && owner != null
                && (current.toString().equals(owner.getName())
                || canStore(current, owner.getType()));
    }

    private static boolean compatibleArrayElement(Type declared,
                                                   SootClass selected) {
        return declared instanceof RefType && selected != null
                && (declared.toString().equals(selected.getName())
                || canStore(selected.getType(), declared));
    }

    /** An absent hierarchy answers "no", never an exception. */
    private static boolean canStore(Type source, Type target) {
        try {
            return Scene.v().getOrMakeFastHierarchy().canStoreType(
                    source, target);
        } catch (RuntimeException unavailableHierarchy) {
            return false;
        }
    }

    private static SootField exactField(String signature) {
        FieldPathSpec.DeclaredField declared =
                FieldPathSpec.declaredField(signature);
        if (declared == null) return null;
        return CausynthStaticFacts.field(
                Scene.v().getSootClassUnsafe(declared.owner()),
                field -> declared.signature().equals(field.getSignature())
                        && !field.isStatic());
    }

    private static ProtocolPortMapping port(
            String name, int clientArgument, int serverParameter,
            SootMethod client, SootMethod server) {
        if (clientArgument < 0
                || clientArgument >= client.getParameterCount()
                || serverParameter < 0
                || serverParameter >= server.getParameterCount()) {
            throw new IllegalArgumentException(
                    "protocol request argument index is out of range");
        }
        if (!client.getParameterType(clientArgument).equals(
                server.getParameterType(serverParameter))) {
            throw new IllegalArgumentException(
                    "mapped request types differ");
        }
        return new ProtocolPortMapping(name, clientArgument,
                serverParameter);
    }

    private static String string(JsonObject object, String field) {
        if (object == null || !object.has(field)
                || object.get(field).isJsonNull()) {
            return "";
        }
        return object.get(field).getAsString().trim();
    }

}

final class ProtocolStubMapping {
    final String id;
    final String transport;
    final String clientStub;
    final String serverStub;
    final String clientOwner;
    final List<ProtocolPortMapping> request;
    final boolean response;
    final List<ResponseComponentMapping> responseComponents;

    ProtocolStubMapping(String id, String transport, String clientStub,
                        String serverStub, String clientOwner,
                        List<ProtocolPortMapping> request,
                        boolean response,
                        List<ResponseComponentMapping> responseComponents) {
        this.id = id;
        this.transport = transport;
        this.clientStub = clientStub;
        this.serverStub = serverStub;
        this.clientOwner = clientOwner;
        this.request = Collections.unmodifiableList(
                new ArrayList<>(request));
        this.response = response;
        this.responseComponents = Collections.unmodifiableList(
                new ArrayList<>(responseComponents));
    }
}

final class ResponseComponentMapping {
    final String name;
    final String javaType;
    final List<ResponsePathStep> path;

    ResponseComponentMapping(String name, String javaType,
                             List<ResponsePathStep> path) {
        this.name = name;
        this.javaType = javaType;
        this.path = Collections.unmodifiableList(new ArrayList<>(path));
    }
}

/** One fully lowered response navigation step. */
final class ResponsePathStep {
    static final String FIELD = "FIELD";
    static final String UNIQUE_ARRAY_ELEMENT = "UNIQUE_ARRAY_ELEMENT";

    final String kind;
    final String declaration;
    final String elementType;

    private ResponsePathStep(String kind, String declaration,
                             String elementType) {
        this.kind = kind;
        this.declaration = declaration;
        this.elementType = elementType;
    }

    static ResponsePathStep field(String declaration) {
        return new ResponsePathStep(FIELD, declaration, "");
    }

    static ResponsePathStep uniqueArrayElement(String elementType) {
        return new ResponsePathStep(UNIQUE_ARRAY_ELEMENT, "", elementType);
    }

    Map<String, Object> row() {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("kind", kind);
        if (!declaration.isEmpty()) row.put("declaration", declaration);
        if (!elementType.isEmpty()) row.put("elementType", elementType);
        return row;
    }

    String identity() {
        return kind + ":" + (declaration.isEmpty()
                ? elementType : declaration);
    }

    String leafSegment() {
        if (FIELD.equals(kind)) {
            FieldPathSpec.DeclaredField field =
                    FieldPathSpec.declaredField(declaration);
            return field == null ? "" : field.name();
        }
        return "[" + elementType + "]";
    }
}

final class ProtocolPortMapping {
    final String name;
    final int clientArgument;
    final int serverParameter;

    ProtocolPortMapping(String name, int clientArgument,
                        int serverParameter) {
        this.name = name;
        this.clientArgument = clientArgument;
        this.serverParameter = serverParameter;
    }
}
