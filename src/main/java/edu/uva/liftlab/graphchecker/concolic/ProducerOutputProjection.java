package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;

import java.util.Collections;
import java.util.Set;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Exact target-first projection of one reusable producer relation. */
public final class ProducerOutputProjection {
    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "SELECTED_PRODUCER_OUTPUT_PROJECTION";

    private final JsonObject encoded;
    private final Set<String> outputPorts;
    private final Set<String> edgeIds;

    private ProducerOutputProjection(JsonObject encoded) {
        this.encoded = encoded.deepCopy();
        if (integer(encoded, "schemaVersion", -1) != SCHEMA_VERSION
                || !KIND.equals(string(encoded, "kind"))) {
            throw new IllegalArgumentException(
                    "producer projection requires schemaVersion "
                            + SCHEMA_VERSION + " and kind " + KIND);
        }
        require("campaignId");
        require("regionId");
        require("logicalRegionId");
        require("goalId");
        require("pathSeedKey");
        outputPorts = strings(encoded, "outputPorts");
        edgeIds = strings(encoded, "edgeIds");
        if (outputPorts.isEmpty() || edgeIds.isEmpty()) {
            throw new IllegalArgumentException(
                    "producer projection requires outputs and exact edges");
        }
    }

    public static ProducerOutputProjection create(
            String campaignId, String regionId, String logicalRegionId,
            String goalId, String pathSeedKey, Set<String> outputPorts,
            Set<String> edgeIds) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("kind", KIND);
        result.addProperty("campaignId", required(campaignId,
                "campaignId"));
        result.addProperty("regionId", required(regionId, "regionId"));
        result.addProperty("logicalRegionId", required(logicalRegionId,
                "logicalRegionId"));
        result.addProperty("goalId", required(goalId, "goalId"));
        result.addProperty("pathSeedKey", required(pathSeedKey,
                "pathSeedKey"));
        result.add("outputPorts", encode(outputPorts, "outputPorts"));
        result.add("edgeIds", encode(edgeIds, "edgeIds"));
        return new ProducerOutputProjection(result);
    }

    public static ProducerOutputProjection decode(JsonObject encoded) {
        if (encoded == null) {
            throw new IllegalArgumentException(
                    "producer projection is required");
        }
        return new ProducerOutputProjection(encoded);
    }

    public JsonObject json() { return encoded.deepCopy(); }

    public String campaignId() { return string(encoded, "campaignId"); }

    public Set<String> outputPorts() { return outputPorts; }

    public Set<String> edgeIds() { return edgeIds; }

    public void requireMatches(RegionInstancePlan.Goal goal) {
        if (goal == null || !goal.kind().capturesOutputRelation()
                || !string(encoded, "regionId").equals(
                goal.plan().regionId())
                || !string(encoded, "logicalRegionId").equals(
                goal.plan().logicalRegionId())
                || !string(encoded, "goalId").equals(goal.goalId())
                || !string(encoded, "pathSeedKey").equals(
                firstNonBlank(goal.pathSeedKey(), goal.goalId()))) {
            throw new IllegalArgumentException(
                    "producer projection does not match selected goal");
        }
    }

    private void require(String field) {
        required(string(encoded, field), field);
    }

    private static Set<String> strings(JsonObject source, String field) {
        TreeSet<String> result = new TreeSet<>();
        for (JsonElement element : array(source, field)) {
            if (!element.isJsonPrimitive()
                    || !element.getAsJsonPrimitive().isString()) {
                throw new IllegalArgumentException(field
                        + " must contain strings");
            }
            String value = required(element.getAsString(), field);
            if (!result.add(value)) {
                throw new IllegalArgumentException("duplicate " + field
                        + " member " + value);
            }
        }
        return Collections.unmodifiableSet(result);
    }

    private static JsonArray encode(Set<String> source, String field) {
        if (source == null) {
            throw new IllegalArgumentException(field + " is required");
        }
        JsonArray result = new JsonArray();
        for (String value : new TreeSet<>(source)) {
            result.add(required(value, field));
        }
        return result;
    }

    private static String required(String value, String field) {
        String result = value == null ? "" : value.trim();
        if (result.isEmpty()) {
            throw new IllegalArgumentException(field + " is required");
        }
        return result;
    }
}
