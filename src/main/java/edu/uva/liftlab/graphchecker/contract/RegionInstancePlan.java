package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Execution goals for one causal-skeleton region occurrence. */
public final class RegionInstancePlan {
    private static final String[] RETIRED_FIELDS = {
            "regionInstanceId", "rootCallId", "logicalRegionId",
            "logicalInstanceCount", "summaryReuseKey", "occurrences",
            "occurrenceInstantiationCatalog", "logicalRootCallIds",
            "logicalActivationIds"
    };

    private final JsonObject encoded;
    private final List<Goal> goals;

    private RegionInstancePlan(JsonObject source) {
        encoded = source.deepCopy();
        rejectRetired(encoded, "region plan");
        require(sourceKey(), "sourceKey");
        require(occurrenceId(), "occurrenceId");
        require(relationKey(), "relationKey");
        require(relationContractHash(), "relationContractHash");
        require(regionId(), "regionId");

        List<Goal> decoded = new ArrayList<>();
        Set<String> ids = new LinkedHashSet<>();
        for (JsonElement element : array(encoded, "closureGoals")) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "closureGoals must contain objects for "
                                + occurrenceId());
            }
            Goal goal = new Goal(this, element.getAsJsonObject());
            if (!ids.add(goal.goalId())) {
                throw new IllegalArgumentException(
                        "closure goal ids must be unique for "
                                + occurrenceId());
            }
            decoded.add(goal);
        }
        goals = Collections.unmodifiableList(decoded);
    }

    public static RegionInstancePlan decode(JsonObject encoded) {
        if (encoded == null) {
            throw new IllegalArgumentException("region plan is required");
        }
        return new RegionInstancePlan(encoded);
    }

    public JsonObject json() { return encoded.deepCopy(); }

    public String sourceKey() { return string(encoded, "sourceKey"); }

    public String occurrenceId() { return string(encoded, "occurrenceId"); }

    public String relationKey() { return string(encoded, "relationKey"); }

    public String relationContractHash() {
        return string(encoded, "relationContractHash");
    }

    public String regionId() { return string(encoded, "regionId"); }

    public boolean containsOccurrence(String candidate) {
        return occurrenceId().equals(candidate == null ? ""
                : candidate.trim());
    }

    public List<Goal> goals() { return goals; }

    void writeTaskIdentityTo(JsonObject target) {
        target.addProperty("sourceKey", sourceKey());
        target.addProperty("occurrenceId", occurrenceId());
        target.addProperty("relationKey", relationKey());
        target.addProperty("relationContractHash", relationContractHash());
        target.addProperty("regionId", regionId());
        copyIfPresent(encoded, target, "rootSelector");
        copyIfPresent(encoded, target, "targetMethod");
    }

    public static final class Goal {
        private final RegionInstancePlan plan;
        private final JsonObject encoded;
        private final ClosureGoalKind kind;
        private final Set<String> runtimeDefinitionMethods;
        private final OutputClosureContract outputClosure;

        private Goal(RegionInstancePlan plan, JsonObject source) {
            this.plan = plan;
            this.encoded = source.deepCopy();
            rejectRetired(encoded, "closure goal");
            rejectField(encoded, "executionOccurrence", "closure goal");
            require(goalId(), "goalId");
            try {
                kind = ClosureGoalKind.fromGoal(encoded);
            } catch (RuntimeException invalid) {
                throw new IllegalArgumentException(
                        "goal kind must be OUTPUT_RELATION_CLOSURE or "
                                + "TARGET_REACH_CLOSURE", invalid);
            }
            runtimeDefinitionMethods = decodeRuntimeDefinitionMethods();
            outputClosure = encoded.has(OutputClosureContract.FIELD)
                    ? decodeOutputClosure() : null;
            if (kind.capturesTargetReach() && outputClosure != null) {
                throw new IllegalArgumentException(
                        "target reach goal must not contain outputClosure");
            }
        }

        public RegionInstancePlan plan() { return plan; }

        public String goalId() { return string(encoded, "goalId"); }

        public String pathSeedKey() {
            return string(encoded, "pathSeedKey");
        }

        public ClosureGoalKind kind() { return kind; }

        public boolean replayable() {
            String state = admissionState();
            return "READY".equals(state) || "DISCOVERED".equals(state);
        }

        public String admissionState() {
            return string(object(encoded, "admission"), "state");
        }

        public JsonArray admissionBlockers() {
            return array(object(encoded, "admission"), "blockers");
        }

        public Set<String> runtimeDefinitionMethods() {
            return runtimeDefinitionMethods;
        }

        public OutputClosureContract outputClosure() {
            return outputClosure;
        }

        public void rejectOutputClosure() {
            if (outputClosure != null) {
                throw new IllegalArgumentException(
                        "outputClosure requires OUTPUT_RELATION_CLOSURE");
            }
        }

        public JsonArray symbolize() {
            return array(encoded, "symbolize").deepCopy();
        }

        public JsonArray branches() {
            return array(encoded, "branches").deepCopy();
        }

        public JsonArray edgeBindings() {
            return array(encoded, "edgeBindings").deepCopy();
        }

        void writeTaskIdentityTo(JsonObject target) {
            plan.writeTaskIdentityTo(target);
        }

        void writeTaskPayloadTo(JsonObject target) {
            target.addProperty("goalId", goalId());
            if (encoded.has("pathSeedKey")) {
                target.add("pathSeedKey",
                        encoded.get("pathSeedKey").deepCopy());
            }
            if (outputClosure != null) {
                target.add(OutputClosureContract.FIELD,
                        outputClosure.toJson());
            }
        }

        /** Stable grouping key for planner goals before relation keys exist. */
        public static String semanticGoalKey(
                JsonObject goal, String regionId) {
            List<String> outputs = new ArrayList<>();
            for (JsonElement element : array(object(goal,
                    OutputClosureContract.FIELD), "members")) {
                if (!element.isJsonObject()) continue;
                String port = string(object(element.getAsJsonObject(),
                        "output"), "portId");
                if (!port.isEmpty()) outputs.add(port);
            }
            Collections.sort(outputs);
            List<String> inputs = new ArrayList<>();
            for (JsonElement element : array(goal, "symbolize")) {
                if (!element.isJsonObject()) continue;
                String port = string(element.getAsJsonObject(), "portId");
                if (port.isEmpty()) {
                    port = string(element.getAsJsonObject(), "symbol");
                }
                if (!port.isEmpty()) inputs.add(port);
            }
            Collections.sort(inputs);
            return string(goal, "kind") + "\n" + regionId + "\n"
                    + string(goal, "pathSeedKey") + "\n" + outputs
                    + "\n" + inputs + "\n" + admissionIdentity(goal);
        }

        private OutputClosureContract decodeOutputClosure() {
            OutputClosureContract contract = OutputClosureCodec.decode(encoded);
            OutputClosureContract.Producer producer = contract.producer();
            if (!plan.regionId().equals(producer.regionId())
                    || !plan.relationKey().equals(producer.relationKey())
                    || !plan.relationContractHash().equals(
                    producer.contractHash())) {
                throw new IllegalArgumentException(
                        "outputClosure producer conflicts with relation");
            }
            return contract;
        }

        private Set<String> decodeRuntimeDefinitionMethods() {
            JsonElement definitions = encoded.get("runtimeDefinitionMethods");
            if (definitions == null || !definitions.isJsonArray()) {
                throw new IllegalArgumentException(
                        "closure goal requires runtimeDefinitionMethods array: "
                                + plan.occurrenceId());
            }
            Set<String> methods = new LinkedHashSet<>();
            for (JsonElement method : definitions.getAsJsonArray()) {
                if (!method.isJsonPrimitive()
                        || !method.getAsJsonPrimitive().isString()
                        || method.getAsString().trim().isEmpty()) {
                    throw new IllegalArgumentException(
                            "runtimeDefinitionMethods must contain nonempty "
                                    + "strings: " + plan.occurrenceId());
                }
                methods.add(method.getAsString().trim());
            }
            return Collections.unmodifiableSet(methods);
        }

        private static String admissionIdentity(JsonObject goal) {
            JsonObject admission = object(goal, "admission");
            List<String> blockers = new ArrayList<>();
            for (JsonElement element : array(admission, "blockers")) {
                if (element.isJsonPrimitive()
                        && element.getAsJsonPrimitive().isString()) {
                    blockers.add(element.getAsString());
                }
            }
            Collections.sort(blockers);
            return string(admission, "state") + "\n" + blockers;
        }
    }

    private static void rejectRetired(JsonObject value, String label) {
        for (String field : RETIRED_FIELDS) {
            rejectField(value, field, label);
        }
    }

    private static void rejectField(
            JsonObject value, String field, String label) {
        if (value.has(field)) {
            throw new IllegalArgumentException(label
                    + " contains retired field " + field);
        }
    }

    private static String require(String value, String field) {
        String result = value == null ? "" : value.trim();
        if (result.isEmpty()) {
            throw new IllegalArgumentException(
                    "region plan requires " + field);
        }
        return result;
    }

    private static void copyIfPresent(
            JsonObject source, JsonObject target, String field) {
        if (source.has(field)) {
            target.add(field, source.get(field).deepCopy());
        }
    }
}
