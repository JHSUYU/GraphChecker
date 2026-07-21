package edu.uva.liftlab.graphchecker.causynth;

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
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Exact runtime interface-dispatch observations used by an optional
 * static-analysis refinement pass.
 *
 * <p>The evidence file is never discovered by walking old output directories:
 * callers must pass one explicit artifact via {@code causynth.runtime.call.edges}
 * (or {@code CAUSYNTH_RUNTIME_CALL_EDGES}).</p>
 */
final class RuntimeDispatchEvidence {
    private final String source;
    private final Map<String, RuntimeDispatchObservation> observations;
    private final int rowCount;
    private final int rejectedRowCount;

    private RuntimeDispatchEvidence(
            String source,
            Map<String, RuntimeDispatchObservation> observations,
            int rowCount, int rejectedRowCount) {
        this.source = source;
        this.observations = observations;
        this.rowCount = rowCount;
        this.rejectedRowCount = rejectedRowCount;
    }

    static RuntimeDispatchEvidence fromConfiguration() throws IOException {
        String configured = value(firstNonBlank(
                System.getProperty("causynth.runtime.call.edges"),
                System.getenv("CAUSYNTH_RUNTIME_CALL_EDGES")));
        if (configured.isEmpty()) {
            return new RuntimeDispatchEvidence("", new LinkedHashMap<>(),
                    0, 0);
        }
        Path path = Paths.get(configured).toAbsolutePath().normalize();
        if (!Files.isRegularFile(path)) {
            throw new IOException("Runtime call-edge evidence not found: "
                    + path);
        }
        Map<String, RuntimeDispatchObservation> observations =
                new LinkedHashMap<>();
        int rows = 0;
        int rejected = 0;
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                String trimmed = line.trim();
                if (trimmed.isEmpty()) {
                    continue;
                }
                rows++;
                JsonObject row;
                try {
                    JsonElement parsed = JsonParser.parseString(trimmed);
                    if (!parsed.isJsonObject()) {
                        rejected++;
                        continue;
                    }
                    row = parsed.getAsJsonObject();
                } catch (RuntimeException malformed) {
                    rejected++;
                    continue;
                }
                String event = jsonString(row, "event");
                String caller = jsonString(row, "caller");
                String siteId = jsonString(row, "siteId");
                String declared = jsonString(row, "declaredCallee");
                String actual = jsonString(row, "actualCallee");
                String level = jsonString(row, "evidenceLevel");
                if (!"RUNTIME_CALL_EDGE".equals(event)
                        || !"CALLSITE_CORRELATED".equals(level)
                        || caller.isEmpty() || siteId.isEmpty()
                        || declared.isEmpty() || actual.isEmpty()
                        || !siteId.startsWith(caller + "#u")) {
                    rejected++;
                    continue;
                }
                String key = key(caller, siteId, declared);
                RuntimeDispatchObservation observation =
                        observations.computeIfAbsent(key,
                                ignored -> new RuntimeDispatchObservation(
                                        caller, siteId, declared));
                observation.actualCallees.add(actual);
            }
        }
        return new RuntimeDispatchEvidence(path.toString(), observations,
                rows, rejected);
    }

    RuntimeDispatchObservation lookup(String caller, String siteId,
                                      String declared) {
        return observations.get(key(caller, siteId, declared));
    }

    boolean configured() {
        return !source.isEmpty();
    }

    String source() {
        return source;
    }

    int rowCount() {
        return rowCount;
    }

    int siteCount() {
        return observations.size();
    }

    int rejectedRowCount() {
        return rejectedRowCount;
    }

    private static String key(String caller, String siteId,
                              String declared) {
        return value(caller) + "\n" + value(siteId) + "\n"
                + value(declared);
    }

    private static String jsonString(JsonObject object, String field) {
        if (object == null || !object.has(field)
                || object.get(field).isJsonNull()
                || !object.get(field).isJsonPrimitive()) {
            return "";
        }
        try {
            return object.get(field).getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static String firstNonBlank(String... values) {
        for (String candidate : values) {
            if (candidate != null && !candidate.trim().isEmpty()) {
                return candidate.trim();
            }
        }
        return null;
    }

    private static String value(Object candidate) {
        return candidate == null || "null".equals(String.valueOf(candidate))
                ? "" : String.valueOf(candidate);
    }
}

final class RuntimeDispatchObservation {
    final String caller;
    final String siteId;
    final String declaredCallee;
    final Set<String> actualCallees = new LinkedHashSet<>();

    RuntimeDispatchObservation(String caller, String siteId,
                               String declaredCallee) {
        this.caller = caller;
        this.siteId = siteId;
        this.declaredCallee = declaredCallee;
    }
}

final class RuntimeDispatchSelection {
    final String siteId;
    final List<String> targets;
    final Set<String> actualCallees;
    final String source;
    final String reason;
    final boolean runtimeSelected;

    private RuntimeDispatchSelection(String siteId,
                                     Collection<String> targets,
                                     Collection<String> actualCallees,
                                     String source, String reason,
                                     boolean runtimeSelected) {
        this.siteId = value(siteId);
        this.targets = new ArrayList<>(targets);
        this.actualCallees = new LinkedHashSet<>(actualCallees);
        this.source = value(source);
        this.reason = value(reason);
        this.runtimeSelected = runtimeSelected;
    }

    static RuntimeDispatchSelection staticFallback(
            String siteId, Collection<String> targets) {
        return new RuntimeDispatchSelection(siteId, targets,
                Collections.emptySet(), "", "", false);
    }

    static RuntimeDispatchSelection runtimeUnique(
            String siteId, String target, String source) {
        return new RuntimeDispatchSelection(siteId,
                Collections.singletonList(target),
                Collections.singleton(target), source, "", true);
    }

    static RuntimeDispatchSelection blocked(
            String siteId, Collection<String> actualCallees,
            String reason) {
        return new RuntimeDispatchSelection(siteId,
                Collections.emptyList(), actualCallees, "", reason, true);
    }

    RuntimeDispatchSelection withReason(String updatedReason) {
        return new RuntimeDispatchSelection(siteId, targets, actualCallees,
                source, updatedReason, runtimeSelected);
    }

    boolean unique() {
        return runtimeSelected && reason.isEmpty() && targets.size() == 1;
    }

    boolean blocked() {
        return !reason.isEmpty();
    }

    private static String value(Object candidate) {
        return candidate == null || "null".equals(String.valueOf(candidate))
                ? "" : String.valueOf(candidate);
    }
}
