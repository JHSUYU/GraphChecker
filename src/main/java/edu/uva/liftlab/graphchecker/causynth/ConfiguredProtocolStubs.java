package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import soot.SootMethod;
import soot.VoidType;
import edu.uva.liftlab.graphchecker.contract.ProtocolBoundaryScalarConfig;

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

/**
 * Explicit protocol-layer call bridges.  These rows describe remote or
 * transport-mediated value flow; they are never inferred from class names or
 * Java implementation relationships.
 */
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
        ProtocolBoundaryScalarConfig.read(path);

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
                for (ProtocolStubMapping existing : byServer.getOrDefault(
                        mapping.serverStub, Collections.emptyList())) {
                    if (existing.serverContext != mapping.serverContext) {
                        throw new IOException("Conflicting serverContext for "
                                + mapping.serverStub + " at " + path + ":"
                                + lineNumber);
                    }
                }
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

    boolean isExecutionEntryServerStub(String method) {
        if (method == null) {
            return false;
        }
        for (ProtocolStubMapping mapping : sources(method)) {
            if (mapping.serverContext
                    == ProtocolServerContext.EXECUTION_ENTRY) {
                return true;
            }
        }
        return false;
    }

    boolean isNestedCallServerStub(String method) {
        if (method == null) {
            return false;
        }
        for (ProtocolStubMapping mapping : sources(method)) {
            if (mapping.serverContext == ProtocolServerContext.NESTED_CALL) {
                return true;
            }
        }
        return false;
    }

    boolean isClientOwner(String owner) {
        return clientOwners.contains(owner);
    }

    private static ConfiguredProtocolStubs empty() {
        return new ConfiguredProtocolStubs(new LinkedHashMap<>(),
                new LinkedHashMap<>(), new LinkedHashSet<>(),
                Collections.emptyList());
    }

    private static ProtocolStubMapping parse(JsonObject row,
                                             Map<String, SootMethod> methods) {
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
        String id = string(row, "id");
        if (id.isEmpty()) {
            id = clientStub + " -> " + serverStub;
        }
        String encodedServerContext = string(row, "serverContext");
        ProtocolServerContext serverContext;
        if (encodedServerContext.isEmpty()) {
            serverContext = ProtocolServerContext.EXECUTION_ENTRY;
        } else {
            try {
                serverContext = ProtocolServerContext.valueOf(
                        encodedServerContext);
            } catch (IllegalArgumentException invalid) {
                throw new IllegalArgumentException("serverContext must be "
                        + "EXECUTION_ENTRY or NESTED_CALL: "
                        + encodedServerContext, invalid);
            }
        }
        return new ProtocolStubMapping(id, string(row, "transport"),
                clientStub, serverStub, client.getDeclaringClass().getName(),
                request, response, serverContext);
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

    private static String firstNonBlank(String... values) {
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) {
                return value.trim();
            }
        }
        return null;
    }
}

enum ProtocolServerContext {
    EXECUTION_ENTRY,
    NESTED_CALL
}

final class ProtocolStubMapping {
    final String id;
    final String transport;
    final String clientStub;
    final String serverStub;
    final String clientOwner;
    final List<ProtocolPortMapping> request;
    final boolean response;
    final ProtocolServerContext serverContext;

    ProtocolStubMapping(String id, String transport, String clientStub,
                        String serverStub, String clientOwner,
                        List<ProtocolPortMapping> request,
                        boolean response,
                        ProtocolServerContext serverContext) {
        this.id = id;
        this.transport = transport;
        this.clientStub = clientStub;
        this.serverStub = serverStub;
        this.clientOwner = clientOwner;
        this.request = Collections.unmodifiableList(
                new ArrayList<>(request));
        this.response = response;
        this.serverContext = serverContext;
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
