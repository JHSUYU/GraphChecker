package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.VoidType;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

/**
 * Parses and resolves project-owned RPC topology declarations against the
 * application classes known to Soot.
 *
 * <p>This loader deliberately produces mapping-only records.  It does not
 * infer value equality: runtime endpoint fingerprints remain the authority
 * for promoting a configured topology edge to an equality relationship.</p>
 */
final class ConfiguredRpcTopologyLoader {
    private ConfiguredRpcTopologyLoader() {
    }

    static Result load(Path mappingFile,
                       Map<String, SootClass> classesByName) {
        if (!Files.isRegularFile(mappingFile)) {
            throw new IllegalStateException(
                    "Configured RPC mapping file not found: " + mappingFile);
        }
        List<Mapping> mappings = new ArrayList<>();
        int downstreamDeclarations = 0;
        try (BufferedReader reader = Files.newBufferedReader(mappingFile,
                StandardCharsets.UTF_8)) {
            String line;
            int lineNumber = 0;
            while ((line = reader.readLine()) != null) {
                lineNumber++;
                String trimmed = line.trim();
                if (trimmed.isEmpty() || trimmed.startsWith("#")) {
                    continue;
                }
                JsonElement parsed = JsonParser.parseString(trimmed);
                if (!parsed.isJsonObject()) {
                    throw new IllegalStateException("RPC topology row "
                            + lineNumber + " is not an object");
                }
                JsonObject row = parsed.getAsJsonObject();
                if (jsonInt(row, "schemaVersion", -1) != 1) {
                    throw new IllegalStateException("RPC topology row "
                            + lineNumber
                            + " has unsupported schemaVersion");
                }
                String kind = jsonString(row, "kind");
                if ("DECLARED_RPC_EQUALITY".equals(kind)) {
                    // Region-port declarations are consumed downstream.  A
                    // static pass has no endpoint-instance evidence with
                    // which to promote one to a semantic equality edge.
                    if (jsonString(row, "fromEndpoint").isEmpty()
                            || jsonString(row, "toEndpoint").isEmpty()) {
                        throw new IllegalStateException(
                                "RPC topology row " + lineNumber
                                        + " has incomplete declared endpoints");
                    }
                    downstreamDeclarations++;
                    continue;
                }
                if (!"RPC_TOPOLOGY".equals(kind)) {
                    throw new IllegalStateException("RPC topology row "
                            + lineNumber + " has unsupported kind " + kind);
                }
                JsonObject producer = jsonObject(row, "producer");
                JsonObject publisher = jsonObject(row, "publisher");
                JsonObject consumer = jsonObject(row, "consumer");
                SootMethod source = configuredRpcMethod(classesByName,
                        producer, lineNumber, "producer");
                SootMethod publisherMethod = configuredRpcMethod(
                        classesByName, publisher, lineNumber, "publisher");
                SootMethod targetMethod = configuredRpcMethod(classesByName,
                        consumer, lineNumber, "consumer");
                if (!"RETURN_VALUE".equals(jsonString(producer, "role"))
                        || !"RETURN_VALUE".equals(jsonString(consumer,
                        "role"))) {
                    throw new IllegalStateException("RPC topology row "
                            + lineNumber + " must map return values");
                }
                String channel = jsonString(row, "channel");
                String authority = jsonString(row, "authority");
                String fromCell = jsonString(row, "fromCell");
                String toCell = jsonString(row, "toCell");
                if (channel.isEmpty() || authority.isEmpty()
                        || fromCell.isEmpty() || toCell.isEmpty()) {
                    throw new IllegalStateException("RPC topology row "
                            + lineNumber + " is missing channel, authority, "
                            + "fromCell, or toCell");
                }
                String sourceReturnCell = source.getSignature() + ".return";
                if (!sourceReturnCell.equals(fromCell)) {
                    throw new IllegalStateException("RPC topology row "
                            + lineNumber + " fromCell does not name the "
                            + "resolved producer return: " + fromCell);
                }
                if (source.getReturnType() instanceof VoidType
                        || targetMethod.getReturnType() instanceof VoidType
                        || !source.getReturnType().equals(
                        targetMethod.getReturnType())) {
                    throw new IllegalStateException("RPC topology row "
                            + lineNumber + " producer and consumer return "
                            + "types differ: " + source.getReturnType()
                            + " vs " + targetMethod.getReturnType());
                }
                int payloadIndex = jsonInt(publisher,
                        "payloadParameterIndex", jsonInt(publisher,
                                "argumentIndex", 0));
                if (payloadIndex < 0
                        || payloadIndex >= publisherMethod.getParameterCount()
                        || !source.getReturnType().equals(publisherMethod
                        .getParameterType(payloadIndex))) {
                    throw new IllegalStateException("RPC topology row "
                            + lineNumber + " publisher payload parameter "
                            + payloadIndex + " does not match producer "
                            + "return type " + source.getReturnType());
                }
                SootField transportField = configuredRpcField(classesByName,
                        toCell, lineNumber);
                if (!source.getReturnType().equals(transportField.getType())) {
                    throw new IllegalStateException("RPC topology row "
                            + lineNumber + " transport field type "
                            + transportField.getType()
                            + " does not match producer return type "
                            + source.getReturnType());
                }
                mappings.add(new Mapping(source.getSignature(),
                        sourceReturnCell, targetMethod.getSignature(),
                        targetMethod.getSignature() + ".return",
                        "configured RPC channel " + channel + " authority "
                                + authority + " through publisher "
                                + publisherMethod.getSignature()
                                + " and transport field " + toCell
                                + "; mapping only until runtime endpoint "
                                + "fingerprints establish equality"));
            }
        } catch (IOException | RuntimeException exception) {
            throw new IllegalStateException(
                    "Could not load configured RPC topology " + mappingFile,
                    exception);
        }
        return new Result(mappings, downstreamDeclarations);
    }

    private static SootMethod configuredRpcMethod(
            Map<String, SootClass> classesByName, JsonObject endpoint,
            int lineNumber, String endpointName) {
        String owner = jsonString(endpoint, "owner");
        String name = jsonString(endpoint, "name");
        List<String> parameters = new ArrayList<>();
        JsonElement parameterElement = endpoint == null
                ? null : endpoint.get("parameters");
        if (parameterElement != null && !parameterElement.isJsonNull()
                && !parameterElement.isJsonArray()) {
            throw new IllegalStateException("RPC topology row " + lineNumber
                    + " " + endpointName + " parameters must be an array");
        }
        JsonArray configuredParameters = parameterElement == null
                || parameterElement.isJsonNull()
                ? null : parameterElement.getAsJsonArray();
        if (configuredParameters != null) {
            for (JsonElement parameter : configuredParameters) {
                if (!parameter.isJsonPrimitive()
                        || !parameter.getAsJsonPrimitive().isString()) {
                    throw new IllegalStateException("RPC topology row "
                            + lineNumber + " " + endpointName
                            + " parameters must contain type strings");
                }
                parameters.add(parameter.getAsString());
            }
        } else {
            String parameter = jsonString(endpoint, "parameter");
            if (!parameter.isEmpty()) {
                parameters.add(parameter);
            }
        }
        SootClass ownerClass = classesByName.get(owner);
        List<SootMethod> matches = new ArrayList<>();
        if (ownerClass != null) {
            for (SootMethod method : ownerClass.getMethods()) {
                if (!method.isConcrete() || !name.equals(method.getName())
                        || method.getParameterCount() != parameters.size()) {
                    continue;
                }
                boolean exact = true;
                for (int index = 0; index < parameters.size(); index++) {
                    if (!parameters.get(index).equals(
                            method.getParameterType(index).toString())) {
                        exact = false;
                        break;
                    }
                }
                if (exact) {
                    matches.add(method);
                }
            }
        }
        if (matches.size() != 1) {
            throw new IllegalStateException("RPC topology row " + lineNumber
                    + " " + endpointName + " " + owner + "." + name
                    + parameters + " matched " + matches.size()
                    + " concrete methods");
        }
        return matches.get(0);
    }

    private static SootField configuredRpcField(
            Map<String, SootClass> classesByName, String signature,
            int lineNumber) {
        List<SootField> matches = new ArrayList<>();
        for (SootClass sootClass : classesByName.values()) {
            for (SootField field : sootClass.getFields()) {
                if (signature.equals(field.getSignature())) {
                    matches.add(field);
                }
            }
        }
        if (matches.size() != 1) {
            throw new IllegalStateException("RPC topology row " + lineNumber
                    + " transport field " + signature + " matched "
                    + matches.size() + " fields");
        }
        return matches.get(0);
    }

    private static String jsonString(JsonObject object, String field) {
        if (object == null) {
            return "";
        }
        JsonElement value = object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static JsonObject jsonObject(JsonObject object, String field) {
        if (object == null) {
            return new JsonObject();
        }
        JsonElement value = object.get(field);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static int jsonInt(JsonObject object, String field,
                               int fallback) {
        JsonElement value = object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    static final class Mapping {
        final String sourceMethod;
        final String sourceCell;
        final String targetMethod;
        final String targetCell;
        final String evidence;

        private Mapping(String sourceMethod, String sourceCell,
                        String targetMethod, String targetCell,
                        String evidence) {
            this.sourceMethod = sourceMethod;
            this.sourceCell = sourceCell;
            this.targetMethod = targetMethod;
            this.targetCell = targetCell;
            this.evidence = evidence;
        }
    }

    static final class Result {
        private final List<Mapping> mappings;
        final int downstreamDeclarationCount;

        private Result(List<Mapping> mappings,
                       int downstreamDeclarationCount) {
            this.mappings = Collections.unmodifiableList(
                    new ArrayList<>(mappings));
            this.downstreamDeclarationCount = downstreamDeclarationCount;
        }

        List<Mapping> mappings() {
            return mappings;
        }
    }
}
