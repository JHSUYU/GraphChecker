package edu.uva.liftlab.graphchecker.grey;

import com.google.gson.Gson;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public final class GreyTraceEvidenceIngestor {
    private final Gson gson = new Gson();

    public EvidenceResult ingest(GreyStateAnalysisResult result, Path traceFile) {
        Map<String, List<JsonObject>> observedById = readTraceEvents(traceFile);
        List<Map<String, Object>> evidence = new ArrayList<Map<String, Object>>();
        int observed = 0;
        for (SemanticEvent event : result.getEvents()) {
            String eventId = event.stableId();
            List<JsonObject> observations = observedById.get(eventId);
            boolean isObserved = observations != null && !observations.isEmpty();
            if (isObserved) {
                observed++;
            }
            Map<String, Object> row = new LinkedHashMap<String, Object>();
            row.put("event_id", eventId);
            row.put("event_type", event.getEventType());
            row.put("method", event.getMethod());
            row.put("unit", event.getUnit());
            row.put("static_candidate", true);
            row.put("trace_observed", isObserved);
            row.put("observation_count", isObserved ? observations.size() : 0);
            row.put("confidence", isObserved ? "trace_observed" : "static_only");
            row.put("attributes", event.getAttributes());
            row.put("observations", isObserved ? observations : new ArrayList<JsonObject>());
            evidence.add(row);
        }
        return new EvidenceResult(evidence, result.getEvents().size(), observed, traceFile);
    }

    private Map<String, List<JsonObject>> readTraceEvents(Path traceFile) {
        Map<String, List<JsonObject>> events = new LinkedHashMap<String, List<JsonObject>>();
        if (traceFile == null || !Files.exists(traceFile)) {
            return events;
        }
        try {
            for (String line : Files.readAllLines(traceFile, StandardCharsets.UTF_8)) {
                String trimmed = line.trim();
                if (trimmed.isEmpty()) {
                    continue;
                }
                JsonObject json = new JsonParser().parse(trimmed).getAsJsonObject();
                String eventId = stringField(json, "event_id");
                if (eventId == null || eventId.isEmpty()) {
                    eventId = stringField(json, "eventId");
                }
                if (eventId == null || eventId.isEmpty()) {
                    continue;
                }
                List<JsonObject> bucket = events.get(eventId);
                if (bucket == null) {
                    bucket = new ArrayList<JsonObject>();
                    events.put(eventId, bucket);
                }
                bucket.add(json);
            }
        } catch (IOException exception) {
            throw new IllegalStateException("Failed to read grey trace evidence " + traceFile, exception);
        }
        return events;
    }

    private String stringField(JsonObject json, String name) {
        if (!json.has(name) || json.get(name).isJsonNull()) {
            return "";
        }
        return json.get(name).getAsString();
    }

    public static final class EvidenceResult {
        private final List<Map<String, Object>> evidence;
        private final int staticEvents;
        private final int observedEvents;
        private final Path traceFile;

        EvidenceResult(List<Map<String, Object>> evidence, int staticEvents, int observedEvents, Path traceFile) {
            this.evidence = evidence;
            this.staticEvents = staticEvents;
            this.observedEvents = observedEvents;
            this.traceFile = traceFile;
        }

        public List<Map<String, Object>> getEvidence() {
            return evidence;
        }

        public int getStaticEvents() {
            return staticEvents;
        }

        public int getObservedEvents() {
            return observedEvents;
        }

        public Path getTraceFile() {
            return traceFile;
        }

        public Set<String> observedEventTypes() {
            Set<String> types = new LinkedHashSet<String>();
            for (Map<String, Object> row : evidence) {
                if (Boolean.TRUE.equals(row.get("trace_observed"))) {
                    types.add(String.valueOf(row.get("event_type")));
                }
            }
            return types;
        }

        public String toJson() {
            return new Gson().toJson(evidence);
        }
    }
}
