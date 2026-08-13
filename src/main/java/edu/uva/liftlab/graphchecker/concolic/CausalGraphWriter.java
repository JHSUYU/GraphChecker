package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Emits a selected causal skeleton and its solver witness. */
public final class CausalGraphWriter {
    private CausalGraphWriter() { }

    public static void main(String[] args) throws Exception {
        if (args.length < 6) throw new IllegalArgumentException("usage: runtime-plan source-events schedule composition reach-report output-dir [summary-jsonl ...]");
        List<JsonObject> rows = ArtifactIO.readJsonl(Paths.get(args[0]));
        if (rows.isEmpty() || !rows.get(0).has("edges")) throw new IllegalArgumentException("runtime plan has no edge catalog");
        JsonObject catalog = rows.remove(0);
        List<JsonObject> summaries = new ArrayList<>();
        for (int i = 6; i < args.length; i++) summaries.addAll(ArtifactIO.readJsonl(Paths.get(args[i])));
        JsonObject composition = ArtifactIO.readObject(Paths.get(args[3]));
        JsonObject graph = skeleton(rows, objects(array(catalog, "edges")), ArtifactIO.readJsonl(Paths.get(args[1])), ArtifactIO.readObject(Paths.get(args[2])), composition, summaries);
        Path out = Paths.get(args[5]);
        String json = new GsonBuilder().disableHtmlEscaping().setPrettyPrinting().create().toJson(graph) + "\n";
        ArtifactIO.replace(out.resolve("causal_skeleton.json"), json);
        JsonObject witness = witness(graph, ArtifactIO.readObject(Paths.get(args[4])), composition);
        ArtifactIO.replace(out.resolve("causal_witness.json"), new GsonBuilder().disableHtmlEscaping().setPrettyPrinting().create().toJson(witness) + "\n");
        ArtifactIO.replace(out.resolve("causal_witness.dot"), dot(witness));
    }

    static JsonObject skeleton(List<JsonObject> plans, List<JsonObject> edgeRows, List<JsonObject> sourceEvents, JsonObject schedule, JsonObject composition, List<JsonObject> summaries) {
        JsonArray gaps = new JsonArray();
        Map<String, JsonObject> planById = index(plans, "occurrenceId"), edgeById = index(edgeRows, "edgeId");
        JsonObject selectedTarget = object(schedule, "target");
        Set<String> occurrences = new LinkedHashSet<>(), edgeIds = texts(array(composition, "resolvedEdgeBindings"));
        add(occurrences, string(selectedTarget, "occurrenceId"));
        for (JsonElement value : array(schedule, "producers")) if (value.isJsonObject()) add(occurrences, string(value.getAsJsonObject(), "occurrenceId"));
        for (String id : edgeIds) {
            JsonObject edge = edgeById.get(id);
            if (edge == null) { gap(gaps, "EDGE_UNAVAILABLE", id); continue; }
            add(occurrences, string(edge, "fromOccurrenceId")); add(occurrences, string(edge, "toOccurrenceId"));
        }
        Map<String, JsonObject> nodes = new LinkedHashMap<>(), edges = new LinkedHashMap<>();
        Map<String, String> regionNodes = new LinkedHashMap<>(), sourceNodes = new LinkedHashMap<>();
        Map<String, List<String>> requestRegions = new LinkedHashMap<>();
        for (String occurrence : occurrences) {
            JsonObject plan = planById.get(occurrence);
            if (plan == null) { gap(gaps, "PLAN_UNAVAILABLE", occurrence); continue; }
            String sourceKey = string(plan, "sourceKey");
            if (sourceKey.isEmpty()) gap(gaps, "SOURCE_KEY_UNAVAILABLE", occurrence);
            if ("WORKLOAD_FALLBACK".equals(
                    string(plan, "sourceAuthority"))) {
                gap(gaps, "SOURCE_IDENTITY_FALLBACK", occurrence);
            }
            if (!sourceKey.isEmpty() && !sourceNodes.containsKey(sourceKey)) {
                JsonObject source = node("source:" + hash(sourceKey), "SOURCE");
                copy(source, plan, "sourceKey", "sourceKind", "sourceRole",
                        "sourceId", "sourceEpoch", "sourceAuthority");
                nodes.put(string(source, "id"), source); sourceNodes.put(sourceKey, string(source, "id"));
            }
            JsonObject region = node("region:" + hash(occurrence), "REGION_OCCURRENCE");
            copy(region, plan, "sourceKey", "occurrenceId", "relationKey",
                    "relationContractHash", "regionId", "targetMethod",
                    "requestKey", "requestApi", "sourceAuthority");
            region.addProperty("target", occurrence.equals(string(selectedTarget, "occurrenceId")));
            JsonArray relations = new JsonArray();
            for (JsonObject summary : summaries) {
                if (!string(plan, "relationKey").equals(
                        summaryRelationKey(summary))) {
                    continue;
                }
                relations.add(relationReference(summary));
                String coverageState = or(string(summary,
                        "pathCoverageState"), "CLOSED");
                if (!"CLOSED".equals(coverageState)) {
                    gap(gaps, "RELATION_" + coverageState,
                            string(summary, "summaryId"));
                }
            }
            region.add("symbolicRelations", relations); nodes.put(string(region, "id"), region); regionNodes.put(occurrence, string(region, "id"));
            String requestKey = string(plan, "requestKey");
            if (!requestKey.isEmpty()) {
                requestRegions.computeIfAbsent(requestKey,
                        ignored -> new ArrayList<>()).add(string(region, "id"));
            }
            if (sourceNodes.containsKey(sourceKey)) putEdge(edges, basic("SOURCE_CONTAINS_REGION", sourceNodes.get(sourceKey), string(region, "id"), "OBSERVED_BASELINE"));
        }
        sourceEvents(sourceEvents, sourceNodes, requestRegions, nodes, edges,
                gaps);
        Map<String, JsonArray> assertions = assertions(composition);
        for (String id : edgeIds) {
            JsonObject evidence = edgeById.get(id); if (evidence == null) continue;
            String from = regionNodes.get(string(evidence, "fromOccurrenceId")), to = regionNodes.get(string(evidence, "toOccurrenceId"));
            if (from == null || to == null) { gap(gaps, "EDGE_ENDPOINT_UNAVAILABLE", id); continue; }
            String state = state(evidence, id, gaps), alignment = or(string(evidence, "alignment"), "UNRESOLVED");
            JsonObject edge = basic(or(string(evidence, "transportKind"), string(evidence, "kind"), "CAUSAL_FLOW"), from, to, state);
            copy(edge, evidence, "fromOccurrenceId", "toOccurrenceId", "fromOutputPort", "toInputPort", "fieldPathDeclarations");
            edge.add("selectedEdgeIds", one(id)); edge.add("evidenceIds", unique(array(evidence, "evidenceIds")));
            edge.add("smtAssertions", assertions.containsKey(id) ? assertions.get(id).deepCopy() : new JsonArray());
            edge.add("evidenceStates", one(state)); edge.add("alignmentStates", one(alignment)); edge.addProperty("alignment", alignment); edge.addProperty("style", style(state, alignment));
            if (string(edge, "fromOutputPort").isEmpty() || string(edge, "toInputPort").isEmpty()) gap(gaps, "EDGE_PORT_UNAVAILABLE", id);
            if (array(edge, "evidenceIds").size() == 0) gap(gaps, "EDGE_EVIDENCE_IDS_UNAVAILABLE", id);
            if (!"ALIGNED".equals(alignment)) gap(gaps, "ALIGNMENT_" + alignment, id);
            putEdge(edges, edge);
        }
        String targetOccurrence = string(selectedTarget, "occurrenceId"), targetNode = regionNodes.get(targetOccurrence);
        if (targetNode == null) gap(gaps, "TARGET_UNAVAILABLE", targetOccurrence);
        else {
            JsonObject branch = node("branch:" + hash(targetOccurrence + "\n" + string(composition, "fatalSite")), "CRITICAL_BRANCH");
            branch.addProperty("occurrenceId", targetOccurrence); branch.addProperty("siteId", string(composition, "fatalSite")); branch.addProperty("choice", "FATAL_PATH_ASSERTED");
            branch.add("assertion", object(object(composition, "operandBindingLedger"), "fatalPathAssertion").deepCopy());
            nodes.put(string(branch, "id"), branch); putEdge(edges, basic("REGION_REACHES_TARGET_BRANCH", targetNode, string(branch, "id"), "REPLAY_CONFIRMED"));
        }
        JsonObject result = new JsonObject(), coverage = new JsonObject(), target = selectedTarget.deepCopy();
        result.addProperty("schemaVersion", 1); result.addProperty("kind", "CAUSAL_SKELETON"); result.addProperty("authority", "SELECTED_TARGET_BACKWARD_MODEL_V1");
        target.addProperty("fatalSite", string(composition, "fatalSite")); result.add("target", target); result.add("nodes", values(nodes)); result.add("edges", values(edges));
        coverage.addProperty("selectedOccurrences", occurrences.size()); coverage.addProperty("resolvedOccurrences", regionNodes.size()); coverage.addProperty("selectedEdges", edgeIds.size());
        copy(coverage, composition, "compositionMode", "trustState",
                "pathSetComplete");
        for (JsonElement value : array(composition, "gaps")) {
            gap(gaps, "COMPOSITION_GAP", value.toString());
        }
        coverage.addProperty("gapCount", gaps.size()); coverage.addProperty("relationOrSmtBlocked", false);
        result.add("coverage", coverage); result.add("gaps", gaps); return (JsonObject) CanonicalJson.copy(result);
    }

    private static void sourceEvents(List<JsonObject> events,
                                     Map<String, String> sources,
                                     Map<String, List<String>> requestRegions,
                                     Map<String, JsonObject> nodes,
                                     Map<String, JsonObject> edges,
                                     JsonArray gaps) {
        Set<String> requests = new LinkedHashSet<>();
        for (JsonObject event : events) {
            String kind = string(event, "kind"), source = string(event, "sourceKey"), related = string(event, "relatedSourceKey");
            if ("SOURCE_RESTART".equals(kind)
                    && (sources.containsKey(source)
                    || sources.containsKey(related))) {
                ensureSourceNode(event, false, source, sources, nodes);
                ensureSourceNode(event, true, related, sources, nodes);
                putEdge(edges, basic("SOURCE_RESTARTS_AS",
                        sources.get(source), sources.get(related),
                        "OBSERVED_BASELINE"));
            }
            if (!"REQUEST_BEGIN".equals(kind)) continue;
            String request = scalar(event, "requestId");
            String requestKey = string(event, "requestKey");
            if (!requestRegions.containsKey(requestKey)) continue;
            ensureSourceNode(event, false, source, sources, nodes);
            String key = requestKey.isEmpty()
                    ? source + "\n" + request : requestKey;
            if (request.isEmpty() || requestKey.isEmpty()) {
                gap(gaps, "REQUEST_IDENTITY_INCOMPLETE", source);
                continue;
            }
            if (!requests.add(key)) continue;
            JsonObject api = node("api:" + hash(key), "EXTERNAL_API");
            api.addProperty("sourceKey", source);
            api.addProperty("requestId", request);
            api.addProperty("requestKey", requestKey);
            api.addProperty("apiName", string(event, "apiName"));
            api.addProperty("evidenceState", "OBSERVED_BASELINE");
            nodes.put(string(api, "id"), api);
            putEdge(edges, basic("SOURCE_ISSUES_API_REQUEST",
                    sources.get(source), string(api, "id"),
                    "OBSERVED_BASELINE"));
            for (String region : requestRegions.getOrDefault(requestKey,
                    java.util.Collections.<String>emptyList())) {
                putEdge(edges, basic("API_REQUEST_REACHES_REGION",
                        string(api, "id"), region, "OBSERVED_BASELINE"));
            }
        }
    }

    private static void ensureSourceNode(JsonObject event, boolean related,
                                         String sourceKey,
                                         Map<String, String> sourceNodes,
                                         Map<String, JsonObject> nodes) {
        if (sourceKey.isEmpty() || sourceNodes.containsKey(sourceKey)) return;
        String prefix = related ? "relatedSource" : "source";
        JsonObject source = node("source:" + hash(sourceKey), "SOURCE");
        source.addProperty("sourceKey", sourceKey);
        copyRenamed(source, event, prefix + "Kind", "sourceKind");
        copyRenamed(source, event, prefix + "Role", "sourceRole");
        copyRenamed(source, event, prefix + "Id", "sourceId");
        copyRenamed(source, event, prefix + "Epoch", "sourceEpoch");
        nodes.put(string(source, "id"), source);
        sourceNodes.put(sourceKey, string(source, "id"));
    }

    static JsonObject witness(JsonObject graph, JsonObject reach, JsonObject composition) {
        JsonObject result = new JsonObject(); String reachable = string(object(reach, "reachCondition"), "reachability");
        result.addProperty("schemaVersion", 1); result.addProperty("kind", "CAUSAL_WITNESS"); result.addProperty("verdict", "REACHABLE".equals(reachable) ? "SAT" : "UNREACHABLE".equals(reachable) ? "UNSAT" : "UNKNOWN");
        copy(result, reach, "trustState", "reachCondition"); result.add("target", object(graph, "target").deepCopy()); result.add("rootAssignments", assignments(reach));
        result.add("nodes", array(graph, "nodes").deepCopy()); result.add("edges", array(graph, "edges").deepCopy()); result.add("coverage", object(graph, "coverage").deepCopy()); result.add("gaps", array(graph, "gaps").deepCopy());
        result.add("solverEvidence", object(composition, "operandBindingLedger").deepCopy()); return (JsonObject) CanonicalJson.copy(result);
    }

    private static JsonArray assignments(JsonObject reach) {
        JsonArray result = new JsonArray(), roots = array(object(reach, "roots"), "booleanInputs");
        for (JsonElement value : array(reach, "valuations")) {
            if (!value.isJsonObject() || !"sat".equals(string(value.getAsJsonObject(), "status"))) continue;
            JsonArray values = array(value.getAsJsonObject(), "values");
            for (int i = 0; i < Math.min(roots.size(), values.size()); i++) if (roots.get(i).isJsonObject()) { JsonObject row = new JsonObject(); copy(row, roots.get(i).getAsJsonObject(), "portId", "solverTerm", "javaTypeDescriptor"); row.add("value", values.get(i).deepCopy()); result.add(row); }
            break;
        }
        return result;
    }

    private static JsonObject relationReference(JsonObject summary) {
        JsonObject result = new JsonObject();
        copy(result, summary, "summaryId", "pathCoverageState");
        JsonObject producer = object(object(summary,
                "outputClosure"), "producer");
        copyRenamed(result, producer, "relationKey", "relationKey");
        copyRenamed(result, producer, "contractHash",
                "relationContractHash");
        result.addProperty("caseCount",
                array(object(summary, "regionRelation"), "cases").size());
        return result;
    }

    private static String summaryRelationKey(JsonObject summary) {
        return string(object(object(summary, "outputClosure"), "producer"),
                "relationKey");
    }

    static String dot(JsonObject graph) {
        StringBuilder out = new StringBuilder("digraph causal_witness {\n  rankdir=LR;\n");
        for (JsonElement value : array(graph, "nodes")) { JsonObject node = value.getAsJsonObject(); String type = string(node, "type"), label = "SOURCE".equals(type) ? string(node, "sourceRole") + "\n" + string(node, "sourceId") + " epoch=" + scalar(node, "sourceEpoch") : "REGION_OCCURRENCE".equals(type) ? string(node, "regionId") + "\n" + string(node, "occurrenceId") : "EXTERNAL_API".equals(type) ? string(node, "apiName") : string(node, "siteId"); out.append("  \"").append(escape(string(node, "id"))).append("\" [shape=").append("REGION_OCCURRENCE".equals(type) ? "box" : "CRITICAL_BRANCH".equals(type) ? "diamond" : "oval").append(", label=\"").append(escape(label)).append("\"];\n"); }
        for (JsonElement value : array(graph, "edges")) { JsonObject edge = value.getAsJsonObject(); out.append("  \"").append(escape(string(edge, "from"))).append("\" -> \"").append(escape(string(edge, "to"))).append("\" [style=").append(or(string(edge, "style"), "solid")).append(", label=\"").append(escape(string(edge, "kind"))).append("\"];\n"); }
        return out.append("}\n").toString();
    }

    private static JsonObject node(String id, String type) { JsonObject value = new JsonObject(); value.addProperty("id", id); value.addProperty("type", type); return value; }
    private static JsonObject basic(String kind, String from, String to, String state) { JsonObject edge = new JsonObject(); edge.addProperty("kind", kind); edge.addProperty("from", from); edge.addProperty("to", to); edge.addProperty("evidenceState", state); edge.addProperty("alignment", "ALIGNED"); edge.addProperty("style", style(state, "ALIGNED")); return edge; }
    private static void putEdge(Map<String, JsonObject> edges, JsonObject row) { String key = string(row, "kind") + "\n" + string(row, "from") + "\n" + string(row, "to") + "\n" + string(row, "fromOutputPort") + "\n" + string(row, "toInputPort"); JsonObject prior = edges.get(key); if (prior == null) { row.addProperty("id", "edge:" + hash(key)); edges.put(key, row); return; } for (String field : new String[]{"selectedEdgeIds", "evidenceIds", "smtAssertions", "evidenceStates", "alignmentStates"}) prior.add(field, union(array(prior, field), array(row, field))); if (rank(string(row, "evidenceState")) > rank(string(prior, "evidenceState"))) prior.addProperty("evidenceState", string(row, "evidenceState")); if ("DEVIATED".equals(string(row, "alignment")) || "UNRESOLVED".equals(string(row, "alignment")) && "ALIGNED".equals(string(prior, "alignment"))) prior.addProperty("alignment", string(row, "alignment")); if ("dotted".equals(string(row, "style"))) prior.addProperty("style", "dotted"); else if ("dashed".equals(string(row, "style")) && !"dotted".equals(string(prior, "style"))) prior.addProperty("style", "dashed"); }
    private static int rank(String state) { return "REPLAY_CONFIRMED".equals(state) ? 4 : "OBSERVED_BASELINE".equals(state) ? 3 : "APPROXIMATE".equals(state) ? 2 : 1; }
    private static String state(JsonObject edge, String id, JsonArray gaps) { String state = string(edge, "evidenceState"); if ("OBSERVED_BASELINE".equals(state) || "REPLAY_CONFIRMED".equals(state) || "APPROXIMATE".equals(state) || "UNRESOLVED".equals(state)) { if ("APPROXIMATE".equals(state) || "UNRESOLVED".equals(state)) gap(gaps, "EDGE_" + state, id); return state; } gap(gaps, "EDGE_EVIDENCE_STATE_UNAVAILABLE", id); return "UNRESOLVED"; }
    private static String style(String state, String alignment) { if ("DEVIATED".equals(alignment) || "APPROXIMATE".equals(state)) return "dotted"; return "OBSERVED_BASELINE".equals(state) || "UNRESOLVED".equals(state) || "UNRESOLVED".equals(alignment) ? "dashed" : "solid"; }
    private static Map<String, JsonArray> assertions(JsonObject composition) { Map<String, JsonArray> result = new LinkedHashMap<>(); for (JsonElement value : array(object(composition, "operandBindingLedger"), "edgeAssertions")) if (value.isJsonObject()) result.put(string(value.getAsJsonObject(), "edgeId"), array(value.getAsJsonObject(), "assertionNames").deepCopy()); return result; }
    private static Map<String, JsonObject> index(List<JsonObject> rows, String field) { Map<String, JsonObject> result = new LinkedHashMap<>(); for (JsonObject row : rows) if (!string(row, field).isEmpty()) result.put(string(row, field), row); return result; }
    private static List<JsonObject> objects(JsonArray values) { List<JsonObject> result = new ArrayList<>(); for (JsonElement value : values) if (value.isJsonObject()) result.add(value.getAsJsonObject()); return result; }
    private static JsonArray values(Map<String, JsonObject> values) { JsonArray result = new JsonArray(); for (JsonObject value : values.values()) result.add(value); return result; }
    private static Set<String> texts(JsonArray values) { Set<String> result = new LinkedHashSet<>(); for (JsonElement value : values) if (value.isJsonPrimitive()) add(result, value.getAsString()); return result; }
    private static JsonArray one(String value) { JsonArray result = new JsonArray(); result.add(value); return result; }
    private static JsonArray unique(JsonArray values) { JsonArray result = new JsonArray(); for (String value : texts(values)) result.add(value); return result; }
    private static JsonArray union(JsonArray left, JsonArray right) { JsonArray all = left.deepCopy(); for (JsonElement value : right) all.add(value.deepCopy()); return unique(all); }
    private static void add(Set<String> values, String value) { if (value != null && !value.isEmpty()) values.add(value); }
    private static void copy(JsonObject to, JsonObject from, String... fields) { for (String field : fields) if (from != null && from.has(field) && !from.get(field).isJsonNull()) to.add(field, from.get(field).deepCopy()); }
    private static void copyRenamed(JsonObject to, JsonObject from, String source, String target) { if (from != null && from.has(source) && !from.get(source).isJsonNull()) to.add(target, from.get(source).deepCopy()); }
    private static void gap(JsonArray gaps, String code, String detail) { JsonObject gap = new JsonObject(); gap.addProperty("code", code); if (detail != null && !detail.isEmpty()) gap.addProperty("detail", detail); gaps.add(gap); }
    private static String scalar(JsonObject value, String field) { return value != null && value.has(field) && value.get(field).isJsonPrimitive() ? value.get(field).getAsString() : ""; }
    private static String or(String... values) { for (String value : values) if (value != null && !value.isEmpty()) return value; return ""; }
    private static String hash(String value) { return ArtifactIO.sha256(value).substring(0, 16); }
    private static String escape(String value) { return or(value, "").replace("\\", "\\\\").replace("\"", "\\\"").replace("\r", "").replace("\n", "\\n"); }
}
