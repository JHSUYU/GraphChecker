package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.zip.GZIPInputStream;

import static edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.firstNonBlank;

/** Methods selected by the runtime region-discovery pass. */
final class RegionSkeletonInstrumentationSelection {
    private RegionSkeletonInstrumentationSelection() {
    }

    static Set<String> methodsFromEnvironment() {
        String configured = firstNonBlank(
                System.getProperty("causynth.region.skeletons"),
                System.getenv("CAUSYNTH_REGION_SKELETONS"), "");
        if (configured.isEmpty()) {
            throw new IllegalStateException("REGION_STATE requires "
                    + "causynth.region.skeletons or "
                    + "CAUSYNTH_REGION_SKELETONS");
        }
        Path path = Paths.get(configured);
        Set<String> methods = new LinkedHashSet<>();
        Set<String> regionIds = new LinkedHashSet<>();
        try (BufferedReader reader = reader(path)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) {
                    continue;
                }
                JsonObject row = JsonParser.parseString(line)
                        .getAsJsonObject();
                JsonElement schema = row.get("schemaVersion");
                if (schema == null || !schema.isJsonPrimitive()
                        || !schema.getAsJsonPrimitive().isNumber()
                        || schema.getAsInt() != 2
                        || !"REGION_SKELETON".equals(
                        requiredString(row, "kind"))) {
                    throw new IllegalArgumentException(
                            "not a schema-2 REGION_SKELETON row");
                }
                String regionId = requiredString(row, "regionId");
                String root = requiredString(row, "rootMethod");
                String anchor = requiredString(row, "anchorMethod");
                if (!regionIds.add(regionId)) {
                    throw new IllegalArgumentException(
                            "duplicate REGION_SKELETON regionId: "
                                    + regionId);
                }
                JsonElement encodedMethods = row.get("methods");
                if (encodedMethods == null
                        || !encodedMethods.isJsonArray()
                        || encodedMethods.getAsJsonArray().size() == 0) {
                    throw new IllegalArgumentException(
                            "REGION_SKELETON methods must be a non-empty "
                                    + "array");
                }
                Set<String> regionMethods = new LinkedHashSet<>();
                for (JsonElement method
                        : encodedMethods.getAsJsonArray()) {
                    if (!method.isJsonPrimitive()
                            || !method.getAsJsonPrimitive().isString()
                            || method.getAsString().trim().isEmpty()) {
                        throw new IllegalArgumentException(
                                "REGION_SKELETON methods must be "
                                        + "non-empty strings");
                    }
                    regionMethods.add(method.getAsString());
                }
                if (!regionMethods.contains(root)
                        || !regionMethods.contains(anchor)) {
                    throw new IllegalArgumentException(
                            "REGION_SKELETON methods must contain root "
                                    + "and anchor");
                }
                methods.addAll(regionMethods);
            }
        } catch (IOException | RuntimeException exception) {
            throw new IllegalStateException(
                    "Cannot read runtime region skeletons from " + path,
                    exception);
        }
        if (methods.isEmpty()) {
            throw new IllegalStateException(
                    "Runtime region skeletons selected no methods: " + path);
        }
        return methods;
    }

    private static BufferedReader reader(Path path) throws IOException {
        InputStream input = Files.newInputStream(path);
        try {
            if (path.getFileName().toString().endsWith(".gz")) {
                input = new GZIPInputStream(input);
            }
            return new BufferedReader(new InputStreamReader(input,
                    StandardCharsets.UTF_8));
        } catch (IOException exception) {
            input.close();
            throw exception;
        }
    }

    private static String requiredString(JsonObject row, String name) {
        JsonElement value = row.get(name);
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isString()
                || value.getAsString().trim().isEmpty()) {
            throw new IllegalArgumentException(
                    "REGION_SKELETON requires non-empty " + name);
        }
        return value.getAsString();
    }
}
