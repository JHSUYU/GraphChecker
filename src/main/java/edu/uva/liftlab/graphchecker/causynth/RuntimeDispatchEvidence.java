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
    private final Map<String, Set<String>> calleesByCallsite;

    private RuntimeDispatchEvidence(
            String source,
            Map<String, Set<String>> calleesByCallsite) {
        this.source = source;
        this.calleesByCallsite = calleesByCallsite;
    }

    static RuntimeDispatchEvidence fromConfiguration() throws IOException {
        String configured = value(firstNonBlank(
                System.getProperty("causynth.runtime.call.edges"),
                System.getenv("CAUSYNTH_RUNTIME_CALL_EDGES")));
        if (configured.isEmpty()) {
            return new RuntimeDispatchEvidence("", new LinkedHashMap<>());
        }
        Path path = Paths.get(configured).toAbsolutePath().normalize();
        if (!Files.isRegularFile(path)) {
            throw new IOException("Runtime call-edge evidence not found: "
                    + path);
        }
        Map<String, Set<String>> calleesByCallsite =
                new LinkedHashMap<>();
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                String trimmed = line.trim();
                if (trimmed.isEmpty()) {
                    continue;
                }
                JsonObject row;
                try {
                    JsonElement parsed = JsonParser.parseString(trimmed);
                    if (!parsed.isJsonObject()) {
                        continue;
                    }
                    row = parsed.getAsJsonObject();
                } catch (RuntimeException malformed) {
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
                    continue;
                }
                String key = key(caller, siteId, declared);
                calleesByCallsite.computeIfAbsent(key,
                        ignored -> new LinkedHashSet<>()).add(actual);
            }
        }
        return new RuntimeDispatchEvidence(path.toString(),
                calleesByCallsite);
    }

    Set<String> lookup(String caller, String siteId, String declared) {
        return calleesByCallsite.get(key(caller, siteId, declared));
    }

    String source() {
        return source;
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

final class RuntimeDispatchSelection {
    final String siteId;
    final List<String> targets;
    final String source;
    final boolean blocked;

    private RuntimeDispatchSelection(String siteId,
                                     Collection<String> targets,
                                     String source,
                                     boolean blocked) {
        this.siteId = value(siteId);
        this.targets = new ArrayList<>(targets);
        this.source = value(source);
        this.blocked = blocked;
    }

    static RuntimeDispatchSelection staticFallback(
            String siteId, Collection<String> targets) {
        return new RuntimeDispatchSelection(siteId, targets, "",
                false);
    }

    static RuntimeDispatchSelection runtimeUnique(
            String siteId, String target, String source) {
        return new RuntimeDispatchSelection(siteId,
                Collections.singletonList(target), source, false);
    }

    static RuntimeDispatchSelection blocked(String siteId) {
        return new RuntimeDispatchSelection(siteId,
                Collections.emptyList(), "", true);
    }

    boolean unique() {
        return !blocked && !source.isEmpty() && targets.size() == 1;
    }

    boolean blocked() {
        return blocked;
    }

    private static String value(Object candidate) {
        return candidate == null || "null".equals(String.valueOf(candidate))
                ? "" : String.valueOf(candidate);
    }
}
