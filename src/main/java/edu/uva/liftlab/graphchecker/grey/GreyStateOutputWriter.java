package edu.uva.liftlab.graphchecker.grey;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.TimeUnit;

public final class GreyStateOutputWriter {
    private final Gson gson = new GsonBuilder().setPrettyPrinting().create();

    public void write(GreyStateSpec spec, GreyStateAnalysisResult result) {
        Path out = Paths.get(spec.getOutputDir());
        try {
            Files.createDirectories(out);
            Files.write(out.resolve("events.json"),
                    gson.toJson(result.getEvents()).getBytes(StandardCharsets.UTF_8));
            Files.write(out.resolve("transition_summaries.json"),
                    gson.toJson(result.getTransitionSummaries()).getBytes(StandardCharsets.UTF_8));
            Files.write(out.resolve("unknowns.json"),
                    gson.toJson(result.getUnknowns()).getBytes(StandardCharsets.UTF_8));
            Files.write(out.resolve("grey_cone.json"),
                    gson.toJson(greyCone(result)).getBytes(StandardCharsets.UTF_8));
            Files.write(out.resolve("transport_edges.json"),
                    gson.toJson(transportEdges(result)).getBytes(StandardCharsets.UTF_8));
            Files.write(out.resolve("metadata_flow.json"),
                    gson.toJson(metadataFlow(result)).getBytes(StandardCharsets.UTF_8));
            Files.write(out.resolve("trace_probe_plan.json"),
                    gson.toJson(traceProbePlan(result)).getBytes(StandardCharsets.UTF_8));
            GreyTraceEvidenceIngestor.EvidenceResult evidence =
                    new GreyTraceEvidenceIngestor().ingest(result, out.resolve("trace-events.jsonl"));
            Files.write(out.resolve("evidence.json"),
                    gson.toJson(evidence.getEvidence()).getBytes(StandardCharsets.UTF_8));
            Files.write(out.resolve("evidence_report.md"),
                    evidenceReport(evidence).getBytes(StandardCharsets.UTF_8));
            String smt = new GreyStateSmtGenerator().generate(spec, result);
            Files.write(out.resolve("model.smt2"), smt.getBytes(StandardCharsets.UTF_8));
            Files.write(out.resolve("query.smt2"), smt.getBytes(StandardCharsets.UTF_8));
            String solverResult = solveWithZ3(out.resolve("model.smt2"));
            Files.write(out.resolve("solver_result.txt"), solverResult.getBytes(StandardCharsets.UTF_8));
            Files.write(out.resolve("confidence_report.md"),
                    confidenceReport(result, solverResult).getBytes(StandardCharsets.UTF_8));
            Files.write(out.resolve("witness.md"),
                    witness(result, solverResult).getBytes(StandardCharsets.UTF_8));
            Files.write(out.resolve("README.md"),
                    report(result, solverResult).getBytes(StandardCharsets.UTF_8));
        } catch (IOException exception) {
            throw new IllegalStateException("Failed to write grey-state output to " + out, exception);
        }
    }

    private String report(GreyStateAnalysisResult result, String solverResult) {
        StringBuilder out = new StringBuilder();
        out.append("# Grey-State Extraction Report\n\n");
        out.append("- semantic events: ").append(result.getEvents().size()).append('\n');
        out.append("- transition summaries: ").append(result.getTransitionSummaries().size()).append('\n');
        out.append("- unknown edges: ").append(result.getUnknowns().size()).append('\n');
        out.append("- solver result: ").append(firstLine(solverResult)).append('\n');
        out.append("\nSee `events.json`, `transition_summaries.json`, `unknowns.json`, and `model.smt2`.\n");
        out.append("Additional derived outputs: `grey_cone.json`, `transport_edges.json`, ")
                .append("`metadata_flow.json`, `trace_probe_plan.json`, `evidence.json`, ")
                .append("`evidence_report.md`, `confidence_report.md`, and `witness.md`.\n");
        return out.toString();
    }

    private Map<String, Object> greyCone(GreyStateAnalysisResult result) {
        Map<String, Object> cone = new LinkedHashMap<String, Object>();
        cone.put("fatal_predicates", eventsOf(result, "VALIDATE_MAP_LOOKUP"));
        cone.put("metadata_sources", eventsOf(result, "DERIVE_METADATA"));
        cone.put("cache_events", eventsMatching(result, "CACHE_"));
        cone.put("state_writers", eventsOfAny(result, "MAP_PUT", "MAP_REMOVE", "PROPAGATION_IMPORT"));
        cone.put("transport_events", eventsOfAny(result, "SEND_METADATA", "RECEIVE_METADATA"));
        cone.put("recovery_events", eventsOfAny(result, "RECOVERY_CLEAR_OR_RETRY", "RECOVERY_NO_REPAIR"));
        cone.put("temporal_events", eventsOf(result, "PERIODIC_TRANSITION"));
        cone.put("unknowns", result.getUnknowns());
        return cone;
    }

    private List<Map<String, Object>> transportEdges(GreyStateAnalysisResult result) {
        List<SemanticEvent> sends = eventsOf(result, "SEND_METADATA");
        List<SemanticEvent> receives = eventsOf(result, "RECEIVE_METADATA");
        List<Map<String, Object>> edges = new ArrayList<Map<String, Object>>();
        for (SemanticEvent send : sends) {
            for (SemanticEvent receive : receives) {
                Map<String, Object> edge = new LinkedHashMap<String, Object>();
                edge.put("kind", "TRANSPORT_EDGE");
                edge.put("source_event", send);
                edge.put("sink_event", receive);
                edge.put("boundary", "serialized_metadata");
                edge.put("recognizer", "string_concat_split");
                edge.put("verified_by", Arrays.asList("static", "serialization_idiom"));
                edge.put("confidence", "medium");
                edges.add(edge);
            }
        }
        return edges;
    }

    private List<Map<String, Object>> metadataFlow(GreyStateAnalysisResult result) {
        List<Map<String, Object>> flow = new ArrayList<Map<String, Object>>();
        appendFlow(flow, 1, "derive", deriveForRelevantCache(result),
                "Metadata object is constructed from component-local state.");
        appendFlow(flow, 2, "cache", firstEvent(result, "CACHE_REUSE_WITHOUT_EXPIRY_CHECK"),
                "Relevant cache may return a previously derived object without checking expiry.");
        appendFlow(flow, 3, "cache", firstEvent(result, "CACHE_REFRESH_ON_EXPIRY"),
                "Some paths refresh the cache on expiry; method ownership decides whether this repairs the queried path.");
        appendFlow(flow, 4, "send", firstEvent(result, "SEND_METADATA"),
                "Metadata crosses a boundary through an encoder.");
        appendFlow(flow, 5, "receive", firstEvent(result, "RECEIVE_METADATA"),
                "Metadata is decoded on the validation side.");
        appendFlow(flow, 6, "propagation", firstEvent(result, "PROPAGATION_IMPORT"),
                "Validator-side state can be updated from an imported/exported aggregate.");
        appendFlow(flow, 7, "state_update", preferredEvent(result, "MAP_PUT", "addKeys"),
                "Validator-side state can import or add keys.");
        appendFlow(flow, 8, "state_update", firstEvent(result, "MAP_REMOVE"),
                "Validator-side state can remove keys, typically under an expiry guard.");
        appendFlow(flow, 9, "validate", firstEvent(result, "VALIDATE_MAP_LOOKUP"),
                "Fatal predicate checks metadata against local validator state.");
        appendFlow(flow, 10, "recovery", preferredEvent(result, "RECOVERY_NO_REPAIR", "Dispatcher$PendingMove"),
                "Queried path lacks an effective metadata refresh/retry recovery.");
        return flow;
    }

    private List<Map<String, Object>> traceProbePlan(GreyStateAnalysisResult result) {
        List<Map<String, Object>> probes = new ArrayList<Map<String, Object>>();
        int id = 1;
        for (SemanticEvent event : result.getEvents()) {
            String type = event.getEventType();
            if (type.equals("MAP_PUT") || type.equals("MAP_REMOVE")) {
                probes.add(probe(id++, event, "GREY_STATE_WRITE",
                        "Instrument this state writer in unit tests or mini-cluster tests. "
                                + "The trace should record map identity, key expression, value expression, "
                                + "and dependency tags so propagation can be validated without hard-coded field names."));
            } else if (type.equals("PROPAGATION_IMPORT")) {
                probes.add(probe(id++, event, "GREY_PROPAGATION_EDGE",
                        "Instrument this external-input-to-state edge. The trace should record source object, "
                                + "destination state, key/value hashes, and callback/RPC context."));
            } else if (type.equals("SEND_METADATA")) {
                probes.add(probe(id++, event, "GREY_ENCODE",
                        "Instrument encoder output. The trace should record component order, delimiter, "
                                + "component hashes, and the produced string/byte length."));
            } else if (type.equals("RECEIVE_METADATA")) {
                probes.add(probe(id++, event, "GREY_DECODE",
                        "Instrument decoder input. The trace should record delimiter, parsed index, "
                                + "decoded component hashes, and downstream value bindings."));
            } else if (type.equals("DERIVE_METADATA") || type.startsWith("CACHE_")
                    || type.equals("VALIDATE_MAP_LOOKUP") || type.startsWith("RECOVERY_")
                    || type.equals("PERIODIC_TRANSITION")) {
                probes.add(probe(id++, event, type,
                        "Instrument this semantic event to turn the static summary into executable evidence."));
            }
        }
        return probes;
    }

    private Map<String, Object> probe(int id, SemanticEvent event, String probeType, String purpose) {
        Map<String, Object> probe = new LinkedHashMap<String, Object>();
        probe.put("id", "probe-" + id);
        probe.put("event_id", event.stableId());
        probe.put("probe_type", probeType);
        probe.put("method", event.getMethod());
        probe.put("unit", event.getUnit());
        probe.put("static_event", event.getEventType());
        probe.put("attributes_to_record", event.getAttributes());
        probe.put("purpose", purpose);
        probe.put("evidence_role", "unit_test_or_trace_witness");
        return probe;
    }

    private String evidenceReport(GreyTraceEvidenceIngestor.EvidenceResult evidence) {
        StringBuilder out = new StringBuilder();
        out.append("# Grey Trace Evidence Report\n\n");
        out.append("- trace file: `").append(evidence.getTraceFile()).append("`\n");
        out.append("- static semantic events: ").append(evidence.getStaticEvents()).append('\n');
        out.append("- trace-observed events: ").append(evidence.getObservedEvents()).append('\n');
        out.append("- observed event types: ").append(evidence.observedEventTypes()).append("\n\n");
        if (evidence.getObservedEvents() == 0) {
            out.append("No `trace-events.jsonl` observations were ingested. ")
                    .append("The current model is static/test-selected, not trace-grounded yet.\n\n");
            out.append("Expected JSONL format:\n\n");
            out.append("```json\n");
            out.append("{\"event_id\":\"<id from trace_probe_plan.json>\",")
                    .append("\"event_type\":\"GREY_ENCODE\",")
                    .append("\"test\":\"TestSaslDataTransfer\",")
                    .append("\"values\":{\"component0_hash\":\"...\"}}\n");
            out.append("```\n");
        } else {
            out.append("Trace observations were merged into `evidence.json`. ")
                    .append("Rows with `trace_observed=true` can be used by strict SMT mode later.\n");
        }
        return out.toString();
    }

    private String confidenceReport(GreyStateAnalysisResult result, String solverResult) {
        boolean hasFatal = hasEvent(result, "VALIDATE_MAP_LOOKUP");
        boolean hasSource = hasEvent(result, "DERIVE_METADATA");
        boolean hasStateWriter = hasEvent(result, "MAP_PUT") || hasEvent(result, "MAP_REMOVE");
        boolean hasTransport = hasEvent(result, "SEND_METADATA") && hasEvent(result, "RECEIVE_METADATA");
        boolean hasRecovery = hasEvent(result, "RECOVERY_CLEAR_OR_RETRY") || hasEvent(result, "RECOVERY_NO_REPAIR");
        boolean hasTemporal = hasEvent(result, "PERIODIC_TRANSITION") || hasEvent(result, "TEMPORAL_GUARD");
        boolean hasUnknowns = !result.getUnknowns().isEmpty();
        String level = !hasUnknowns && hasFatal && hasSource && hasStateWriter && hasTransport && hasRecovery
                ? "High"
                : hasFatal && hasSource && hasStateWriter
                ? "Medium"
                : "Low";

        StringBuilder out = new StringBuilder();
        out.append("# Confidence Report\n\n");
        out.append("- warning level: ").append(level).append('\n');
        out.append("- solver result: ").append(firstLine(solverResult)).append('\n');
        out.append("- unknown edges: ").append(result.getUnknowns().size()).append("\n\n");
        out.append("## Cone-Relative Completeness\n\n");
        checklist(out, "fatal predicate variables explained", hasFatal);
        checklist(out, "metadata source discovered", hasSource);
        checklist(out, "validator state writers discovered", hasStateWriter);
        checklist(out, "serialization or transport edge paired", hasTransport);
        checklist(out, "time/loop dynamics represented", hasTemporal);
        checklist(out, "recovery path summarized", hasRecovery);
        checklist(out, "SAT result does not rely on unknown edges", !hasUnknowns);
        out.append("\n## Notes\n\n");
        out.append("- `static` evidence means the event came from Soot/Jimple facts.\n");
        out.append("- This report is cone-relative, not whole-program complete.\n");
        out.append("- Unit-test and trace evidence can be attached later by matching semantic event IDs.\n");
        return out.toString();
    }

    private String witness(GreyStateAnalysisResult result, String solverResult) {
        StringBuilder out = new StringBuilder();
        out.append("# Bounded Grey-State Witness\n\n");
        if (!firstLine(solverResult).equals("sat")) {
            out.append("No SAT witness was produced. Solver result: `")
                    .append(firstLine(solverResult)).append("`.\n");
            return out.toString();
        }
        out.append("The bounded SMT query is SAT. One abstract lifecycle consistent with the extracted summaries is:\n\n");
        int step = 1;
        step = witnessStep(out, step, deriveForRelevantCache(result), "DERIVE_METADATA",
                "A metadata object is derived from component-local state.");
        if (hasEventInMethod(result, "CACHE_REUSE_WITHOUT_EXPIRY_CHECK",
                "org.apache.hadoop.hdfs.server.balancer.KeyManager")) {
            step = witnessStep(out, step, result, "CACHE_REUSE_WITHOUT_EXPIRY_CHECK",
                    "The relevant cache can reuse that metadata without an expiry check.");
        } else {
            step = witnessStep(out, step, result, "CACHE_REFRESH_ON_EXPIRY",
                    "The relevant cache has an expiry-refresh guard.");
        }
        step = witnessStep(out, step, result, "PERIODIC_TRANSITION",
                "A background or periodic transition lets component-local state evolve over time.");
        step = witnessStep(out, step, result, "MAP_REMOVE",
                "The validator-side key map can lose the key referenced by the cached metadata.");
        step = witnessStep(out, step, result, "SEND_METADATA",
                "The sender serializes the cached metadata across a boundary.");
        step = witnessStep(out, step, result, "RECEIVE_METADATA",
                "The receiver decodes the metadata from that boundary representation.");
        step = witnessStep(out, step, result, "VALIDATE_MAP_LOOKUP",
                "The receiver validates the decoded key against its local state.");
        witnessStep(out, step, preferredEvent(result, "RECOVERY_NO_REPAIR", "Dispatcher$PendingMove"),
                "RECOVERY_NO_REPAIR",
                "The selected path has no effective cache-clear/retry recovery.");
        out.append("\nThis witness is abstract: it explains the lifecycle over the bounded SMT variables, ")
                .append("not a complete distributed execution trace.\n");
        return out.toString();
    }

    private String solveWithZ3(Path model) {
        try {
            Process process = new ProcessBuilder("z3", model.toString())
                    .redirectErrorStream(true)
                    .start();
            boolean finished = process.waitFor(10, TimeUnit.SECONDS);
            if (!finished) {
                process.destroyForcibly();
                return "unknown\n; z3 timed out after 10 seconds\n";
            }
            byte[] bytes = readAll(process);
            String output = new String(bytes, StandardCharsets.UTF_8).trim();
            if (output.isEmpty()) {
                return "unknown\n; z3 produced no output\n";
            }
            return output + "\n";
        } catch (Exception exception) {
            return "unknown\n; z3 unavailable or failed: " + exception.getMessage() + "\n";
        }
    }

    private byte[] readAll(Process process) throws IOException {
        byte[] buffer = new byte[4096];
        java.io.ByteArrayOutputStream out = new java.io.ByteArrayOutputStream();
        int read;
        while ((read = process.getInputStream().read(buffer)) >= 0) {
            out.write(buffer, 0, read);
        }
        return out.toByteArray();
    }

    private List<SemanticEvent> eventsOf(GreyStateAnalysisResult result, String eventType) {
        List<SemanticEvent> events = new ArrayList<SemanticEvent>();
        for (SemanticEvent event : result.getEvents()) {
            if (eventType.equals(event.getEventType())) {
                events.add(event);
            }
        }
        return events;
    }

    private List<SemanticEvent> eventsOfAny(GreyStateAnalysisResult result, String... eventTypes) {
        List<String> types = Arrays.asList(eventTypes);
        List<SemanticEvent> events = new ArrayList<SemanticEvent>();
        for (SemanticEvent event : result.getEvents()) {
            if (types.contains(event.getEventType())) {
                events.add(event);
            }
        }
        return events;
    }

    private List<SemanticEvent> eventsMatching(GreyStateAnalysisResult result, String prefix) {
        List<SemanticEvent> events = new ArrayList<SemanticEvent>();
        for (SemanticEvent event : result.getEvents()) {
            if (event.getEventType().startsWith(prefix)) {
                events.add(event);
            }
        }
        return events;
    }

    private SemanticEvent firstEvent(GreyStateAnalysisResult result, String eventType) {
        for (SemanticEvent event : result.getEvents()) {
            if (eventType.equals(event.getEventType())) {
                return event;
            }
        }
        return null;
    }

    private SemanticEvent preferredEvent(GreyStateAnalysisResult result, String eventType, String preferredMethodFragment) {
        for (SemanticEvent event : result.getEvents()) {
            if (eventType.equals(event.getEventType()) && event.getMethod().contains(preferredMethodFragment)) {
                return event;
            }
        }
        return firstEvent(result, eventType);
    }

    private SemanticEvent deriveForRelevantCache(GreyStateAnalysisResult result) {
        SemanticEvent cache = preferredEvent(result, "CACHE_REUSE_WITHOUT_EXPIRY_CHECK",
                "org.apache.hadoop.hdfs.server.balancer.KeyManager");
        if (cache == null) {
            cache = firstEvent(result, "CACHE_REUSE_WITHOUT_EXPIRY_CHECK");
        }
        if (cache == null) {
            cache = firstEvent(result, "CACHE_REFRESH_ON_VALIDITY_GUARD");
        }
        if (cache != null) {
            String metadataType = cache.getAttributes().get("metadataType");
            if (metadataType != null) {
                for (SemanticEvent event : result.getEvents()) {
                    if ("DERIVE_METADATA".equals(event.getEventType())
                            && metadataType.equals(event.getAttributes().get("metadataType"))) {
                        return event;
                    }
                }
            }
        }
        return firstEvent(result, "DERIVE_METADATA");
    }

    private boolean hasEvent(GreyStateAnalysisResult result, String eventType) {
        return firstEvent(result, eventType) != null;
    }

    private boolean hasEventInMethod(GreyStateAnalysisResult result, String eventType, String methodOwner) {
        for (SemanticEvent event : result.getEvents()) {
            if (eventType.equals(event.getEventType()) && event.getMethod().contains(methodOwner)) {
                return true;
            }
        }
        return false;
    }

    private void appendFlow(List<Map<String, Object>> flow, int order, String phase,
            SemanticEvent event, String explanation) {
        if (event == null) {
            return;
        }
        Map<String, Object> entry = new LinkedHashMap<String, Object>();
        entry.put("order", order);
        entry.put("phase", phase);
        entry.put("event", event);
        entry.put("explanation", explanation);
        flow.add(entry);
    }

    private void checklist(StringBuilder out, String label, boolean ok) {
        out.append("- [").append(ok ? "x" : " ").append("] ").append(label).append('\n');
    }

    private int witnessStep(StringBuilder out, int step, GreyStateAnalysisResult result,
            String eventType, String text) {
        SemanticEvent event = firstEvent(result, eventType);
        return witnessStep(out, step, event, eventType, text);
    }

    private int witnessStep(StringBuilder out, int step, SemanticEvent event,
            String eventType, String text) {
        if (event == null) {
            return step;
        }
        out.append(step).append(". ").append(text).append('\n');
        out.append("   - event: `").append(eventType).append("`\n");
        out.append("   - method: `").append(event.getMethod()).append("`\n");
        return step + 1;
    }

    private String firstLine(String text) {
        if (text == null || text.trim().isEmpty()) {
            return "unknown";
        }
        String trimmed = text.trim();
        int newline = trimmed.indexOf('\n');
        return newline >= 0 ? trimmed.substring(0, newline) : trimmed;
    }
}
