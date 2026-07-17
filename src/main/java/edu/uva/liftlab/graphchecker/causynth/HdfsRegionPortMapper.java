package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
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
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * HDFS instance mapper.  It may name generic region ports and attach evidence
 * references, but it is intentionally forbidden from asserting program
 * semantics such as codec invertibility, cache policy, expiry, or membership.
 */
public final class HdfsRegionPortMapper {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();
    private static final String FIXED_REPOSITORY =
            "/Users/lizhenyu/Desktop/study/hadoop";
    private static final String FIXED_COMMIT =
            "ece33208b89a6a06c1b362d10fab31343fe5df13";
    private static final String FIXED_TEST =
            "org.apache.hadoop.hdfs.server.balancer."
                    + "TestBalancerWithEncryptedTransfer#testEncryptedBalancer1";
    private static final String FIXED_EXPERIMENT_PATCH =
            "CAUSYNTH_FIXED_MINIDFSCLUSTER_LOOP_FREE_V1";
    private static final String FIXED_SOURCE_SHA256 =
            "352efc4dd9a3d4e0df4d0840754d63fce1a09509ad947f9c232e24f35372bb93";
    private static final String DATANODE_ALL_KEYS_FIELD =
            "<org.apache.hadoop.hdfs.security.token.block."
                    + "BlockTokenSecretManager: java.util.Map allKeys>";

    private HdfsRegionPortMapper() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        JsonObject result = map(arguments);
        Path parent = arguments.output.toAbsolutePath().getParent();
        if (parent != null) Files.createDirectories(parent);
        Files.write(arguments.output,
                (new GsonBuilder().disableHtmlEscaping().create()
                        .toJson(result) + System.lineSeparator())
                        .getBytes(StandardCharsets.UTF_8),
                StandardOpenOption.CREATE,
                StandardOpenOption.TRUNCATE_EXISTING,
                StandardOpenOption.WRITE);
        System.out.println(GSON.toJson(result));
    }

    public static JsonObject map(Arguments arguments) throws IOException {
        require(arguments.regions, "symbolic regions");
        require(arguments.runtimeReport, "runtime report");
        require(arguments.fatalQueries, "fatal query");
        require(arguments.mergePlan, "merge plan");
        List<JsonObject> regions = readJsonl(arguments.regions);
        JsonObject runtime = readJson(arguments.runtimeReport);
        JsonObject merge = readJson(arguments.mergePlan);
        JsonObject fatal = firstReady(readJsonl(arguments.fatalQueries));

        String fatalRegion = string(fatal, "regionId");
        String balancerRegion = findRegion(regions,
                "KeyManager: org.apache.hadoop.hdfs.security.token.block."
                        + "DataEncryptionKey newDataEncryptionKey");
        JsonObject fatalSchema = region(regions, fatalRegion);
        JsonObject balancerSchema = region(regions, balancerRegion);

        JsonArray mappings = new JsonArray();
        addPort(mappings, "BALANCER_CACHED_KEY_ID", balancerRegion,
                findPort(balancerSchema, "symbolicInputs",
                        "DataEncryptionKeyFactory", "newDataEncryptionKey",
                        "#field:keyId"),
                "STATIC_REGION_PORT_DISCOVERY");
        addPort(mappings, "DATANODE_ALL_KEYS", fatalRegion,
                findExactCellPort(fatalSchema, "symbolicInputs",
                        DATANODE_ALL_KEYS_FIELD),
                "STATIC_EXACT_DECLARED_FIELD_CELL_PLUS_RUNTIME_READ_FROM");
        addPort(mappings, "NAMENODE_CURRENT_KEY_ID", fatalRegion,
                findPort(fatalSchema, "symbolicInputs",
                        "NamenodeProtocol", "getBlockKeys",
                        "#field:currentKey#field:keyId"),
                "STATIC_REGION_PORT_DISCOVERY");
        addPort(mappings, "KEY_UPDATE_INTERVAL", fatalRegion,
                findPort(fatalSchema, "symbolicInputs",
                        "#field:keyUpdateInterval"),
                "STATIC_REGION_PORT_DISCOVERY");
        addPort(mappings, "TOKEN_LIFETIME", fatalRegion,
                findPort(fatalSchema, "symbolicInputs",
                        "#field:tokenLifetime"),
                "STATIC_REGION_PORT_DISCOVERY");
        addPort(mappings, "OBSERVATION_TIME", fatalRegion,
                findPort(fatalSchema, "symbolicInputs",
                        "org.apache.hadoop.util.Time", "now()>.return"),
                "STATIC_REGION_PORT_DISCOVERY");

        JsonArray evidence = new JsonArray();
        evidence.add(evidence("RUNTIME_REPORT", arguments.runtimeReport,
                integer(runtime, "runtimeRegionEdgeValidationCount", -1)));
        evidence.add(evidence("MERGE_PLAN", arguments.mergePlan,
                array(merge, "equalityClasses").size()));
        evidence.add(evidence("FATAL_QUERY", arguments.fatalQueries,
                array(fatal, "constraints").size()));

        JsonArray unresolved = new JsonArray();
        for (JsonElement element : mappings) {
            JsonObject mapping = element.getAsJsonObject();
            if (string(mapping, "portId").isEmpty()) {
                unresolved.add("UNRESOLVED_PORT:" + string(mapping, "role"));
            }
        }

        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "HDFS_REGION_PORT_MAP");
        result.addProperty("mappingOnly", true);
        result.addProperty("semanticAssertionsAllowed", false);
        result.addProperty("eligibleAsRegionSummary", false);
        result.addProperty("eligibleForAutomaticSmt", false);
        result.add("portMappings", mappings);
        result.add("evidenceReferences", evidence);
        result.add("unresolvedMappings", unresolved);
        result.addProperty("complete", unresolved.size() == 0);
        result.addProperty("status", unresolved.size() == 0
                ? "PORT_MAPPING_COMPLETE"
                : "PORT_MAPPING_WITH_GAPS");

        JsonObject scope = new JsonObject();
        scope.addProperty("purpose",
                "ACADEMIC_SOFTWARE_ENGINEERING_AND_PROGRAM_ANALYSIS");
        scope.addProperty("repository", FIXED_REPOSITORY);
        scope.addProperty("commit", FIXED_COMMIT);
        scope.addProperty("test", FIXED_TEST);
        scope.addProperty("experimentalSourcePatch",
                FIXED_EXPERIMENT_PATCH);
        scope.addProperty("experimentalSourceSha256", FIXED_SOURCE_SHA256);
        scope.addProperty("executionBoundary", "LOCAL_MINIDFSCLUSTER_ONLY");
        scope.addProperty("thirdPartySystemsProhibited", true);
        result.add("researchScope", scope);
        return result;
    }

    private static JsonObject evidence(String kind, Path path, int count) {
        JsonObject result = new JsonObject();
        result.addProperty("kind", kind);
        result.addProperty("path", path.toAbsolutePath().toString());
        result.addProperty("observedItemCount", count);
        result.addProperty("semanticConclusion", false);
        return result;
    }

    private static void addPort(JsonArray mappings, String role,
                                String regionId, String portId,
                                String authority) {
        JsonObject result = new JsonObject();
        result.addProperty("role", role);
        result.addProperty("regionId", regionId);
        result.addProperty("portId", portId);
        result.addProperty("authority", authority);
        result.addProperty("formatOrPortMappingOnly", true);
        result.addProperty("semanticAssertion", false);
        mappings.add(result);
    }

    private static String findPort(JsonObject region, String collection,
                                   String... fragments) {
        for (JsonElement element : array(region, collection)) {
            if (!element.isJsonObject()) continue;
            JsonObject port = element.getAsJsonObject();
            String cell = string(port, "cell");
            boolean matches = true;
            for (String fragment : fragments) matches &= cell.contains(
                    fragment);
            if (matches) return firstNonBlank(string(port, "portId"),
                    string(port, "symbol"));
        }
        return "";
    }

    static String findExactCellPort(JsonObject region, String collection,
                                    String exactCell) {
        String selected = "";
        for (JsonElement element : array(region, collection)) {
            if (!element.isJsonObject()) continue;
            JsonObject port = element.getAsJsonObject();
            if (!exactCell.equals(string(port, "cell"))) continue;
            String candidate = firstNonBlank(string(port, "portId"),
                    string(port, "symbol"));
            if (candidate.isEmpty() || !selected.isEmpty()) {
                return "";
            }
            selected = candidate;
        }
        return selected;
    }

    private static String findRegion(List<JsonObject> regions,
                                     String... fragments) {
        for (JsonObject region : regions) {
            boolean all = true;
            for (String fragment : fragments) {
                boolean found = false;
                for (JsonElement method : array(region, "methods")) {
                    found |= method.isJsonPrimitive()
                            && method.getAsString().contains(fragment);
                }
                all &= found;
            }
            if (all) return string(region, "regionId");
        }
        return "";
    }

    private static JsonObject region(List<JsonObject> regions, String id) {
        for (JsonObject value : regions) {
            if (id.equals(string(value, "regionId"))) return value;
        }
        return new JsonObject();
    }

    private static JsonObject firstReady(List<JsonObject> rows) {
        for (JsonObject row : rows) {
            if (bool(row, "readyForSolver", false)) return row;
        }
        return rows.isEmpty() ? new JsonObject() : rows.get(0);
    }

    private static void require(Path path, String label) throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            throw new IOException(label + " not found: " + path);
        }
    }

    private static List<JsonObject> readJsonl(Path path) throws IOException {
        List<JsonObject> result = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) continue;
                JsonElement value = JsonParser.parseString(line);
                if (value.isJsonObject()) result.add(value.getAsJsonObject());
            }
        }
        return result;
    }

    private static JsonObject readJson(Path path) throws IOException {
        JsonElement value = JsonParser.parseString(new String(
                Files.readAllBytes(path), StandardCharsets.UTF_8));
        return value.isJsonObject() ? value.getAsJsonObject()
                : new JsonObject();
    }

    private static JsonArray array(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static String string(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static boolean bool(JsonObject owner, String field,
                                boolean fallback) {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static int integer(JsonObject owner, String field, int fallback) {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static String firstNonBlank(String... values) {
        if (values != null) {
            for (String value : values) {
                if (value != null && !value.trim().isEmpty()) return value;
            }
        }
        return "";
    }

    public static final class Arguments {
        private Path regions;
        private Path runtimeReport;
        private Path fatalQueries;
        private Path mergePlan;
        private Path output;

        public static Arguments parse(String[] argv) {
            Map<String, String> values = new LinkedHashMap<>();
            for (int index = 0; argv != null && index < argv.length; index++) {
                String key = argv[index];
                if (!key.startsWith("--") || index + 1 >= argv.length) {
                    throw new IllegalArgumentException(
                            "Expected --key value, got " + key);
                }
                values.put(key.substring(2), argv[++index]);
            }
            Arguments result = new Arguments();
            result.regions = required(values, "regions");
            result.runtimeReport = required(values, "runtime-report");
            result.fatalQueries = required(values, "fatal-query");
            result.mergePlan = required(values, "merge-plan");
            result.output = required(values, "output");
            return result;
        }

        private static Path required(Map<String, String> values, String key) {
            String value = values.get(key);
            if (value == null || value.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --" + key);
            }
            return Paths.get(value);
        }
    }
}
