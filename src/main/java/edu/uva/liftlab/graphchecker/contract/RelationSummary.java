package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;
import edu.uva.liftlab.graphchecker.concolic.ClosureGoalKind;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Canonical wire carrier for one closed region relation.
 */
public final class RelationSummary {
    private final JsonObject row;
    private final OutputClosureContract outputClosure;
    private final String summaryId;
    private final String regionId;
    private final String regionInstanceId;
    private final List<JsonObject> edgeBindings;

    private RelationSummary(JsonObject row,
                            OutputClosureContract outputClosure) {
        this.row = row;
        this.outputClosure = outputClosure;
        this.summaryId = string(row, "summaryId");
        this.regionId = outputClosure.producer().regionId();
        this.regionInstanceId =
                outputClosure.producer().regionInstanceId();
        List<JsonObject> bindings = new ArrayList<>();
        for (JsonElement element : array(row, "edgeBindings")) {
            if (element.isJsonObject()) {
                bindings.add(element.getAsJsonObject());
            }
        }
        this.edgeBindings = Collections.unmodifiableList(bindings);
    }

    public static RelationSummary decode(JsonObject row) {
        if (row == null) {
            throw new IllegalArgumentException("relation summary is required");
        }
        return new RelationSummary(row.deepCopy(),
                OutputClosureCodec.decode(row));
    }

    public static RelationSummary guardedPathMerge(
            String goalId, OutputClosureContract outputClosure,
            Collection<PathObservation> paths,
            Collection<JsonObject> edgeBindings) {
        List<PathObservation> orderedCases = new ArrayList<>(paths);
        Collections.sort(orderedCases,
                Comparator.comparing(PathObservation::pathKey));
        JsonArray cases = new JsonArray();
        for (PathObservation path : orderedCases) {
            cases.add(pathCase(path));
        }

        Map<String, JsonObject> bindingsByPayload = new LinkedHashMap<>();
        for (JsonObject binding : edgeBindings) {
            bindingsByPayload.put(CanonicalJson.render(binding),
                    binding.deepCopy());
        }
        List<String> bindingKeys =
                new ArrayList<>(bindingsByPayload.keySet());
        Collections.sort(bindingKeys);
        JsonArray bindings = new JsonArray();
        for (String key : bindingKeys) {
            bindings.add(bindingsByPayload.get(key));
        }

        String region = outputClosure.producer().regionId();
        String closureIdentity = CanonicalJson.render(outputClosure.toJson());
        JsonObject relation = new JsonObject();
        relation.addProperty("schemaVersion", 1);
        relation.addProperty("kind", "GUARDED_PATH_MERGE");
        relation.add("cases", cases);
        String relationHash = PathObservation.sha256(region + "\n"
                + closureIdentity + "\n" + CanonicalJson.render(cases)
                + "\n" + CanonicalJson.render(bindings));

        JsonObject merged = new JsonObject();
        merged.addProperty("schemaVersion", 1);
        merged.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
        merged.addProperty("summaryId", "SUMMARY." + region
                + ".MERGED." + relationHash);
        merged.addProperty("regionId", region);
        merged.addProperty("goalId", goalId);
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(merged);
        OutputClosureCodec.writeTo(merged, outputClosure);
        merged.add("edgeBindings", bindings);
        merged.add("regionRelation", relation);
        merged.addProperty("relationallyComplete", true);
        return new RelationSummary(merged, outputClosure);
    }

    public JsonObject toJson() { return row.deepCopy(); }
    public OutputClosureContract outputClosure() { return outputClosure; }
    public String summaryId() { return summaryId; }
    public String regionId() { return regionId; }
    public String regionInstanceId() { return regionInstanceId; }
    public List<JsonObject> edgeBindings() { return edgeBindings; }

    public boolean same(RelationSummary other) {
        return other != null && summaryId.equals(other.summaryId);
    }

    private static JsonObject pathCase(PathObservation path) {
        JsonObject item = new JsonObject();
        item.addProperty("caseId", "CASE." + path.pathKey());
        JsonObject guard = new JsonObject();
        guard.addProperty("kind", "PATH_CONDITION");
        guard.add("conditions", path.pathCondition());
        item.add("guard", guard);
        item.add("outputExpressions", path.outputExpressions());
        path.copyRelationEvidenceTo(item);
        item.addProperty("sourceTaskId", path.sourceTaskId());
        return item;
    }
}
