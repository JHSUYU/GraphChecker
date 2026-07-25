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
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Once-decoded execution goals for one concrete region invocation. */
public final class RegionInstancePlan {
    public enum GoalKind {
        OUTPUT_RELATION_CLOSURE,
        TARGET_REACH_CLOSURE
    }

    private final JsonObject encoded;
    private final String regionId;
    private final String regionInstanceId;
    private final long rootCallId;
    private final boolean hasRootCallId;
    private final int rootOrdinal;
    private final List<Goal> goals;

    private RegionInstancePlan(JsonObject encoded) {
        this.encoded = encoded;
        regionId = string(encoded, "regionId");
        regionInstanceId = string(encoded, "regionInstanceId");
        hasRootCallId = encoded.has("rootCallId");
        rootCallId = longInteger(encoded, "rootCallId", 0L);
        JsonObject root = object(encoded, "rootSelector");
        rootOrdinal = integer(root, "ordinal", Integer.MAX_VALUE);
        if (regionId.isEmpty() || regionInstanceId.isEmpty()) {
            throw new IllegalArgumentException(
                    "region plan requires regionId and regionInstanceId");
        }
        List<Goal> decoded = new ArrayList<>();
        Set<String> ids = new LinkedHashSet<>();
        for (JsonElement element : array(encoded, "closureGoals")) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "closureGoals must contain objects for "
                                + regionInstanceId);
            }
            Goal goal = new Goal(this, element.getAsJsonObject());
            if (!ids.add(goal.goalId())) {
                throw new IllegalArgumentException(
                        "closure goal ids must be nonempty and unique for "
                                + regionInstanceId);
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

    public String regionId() {
        return regionId;
    }

    public String regionInstanceId() {
        return regionInstanceId;
    }

    public int rootOrdinal() {
        return rootOrdinal;
    }

    public List<Goal> goals() {
        return goals;
    }

    void writeTaskIdentityTo(JsonObject target) {
        target.addProperty("regionId", regionId);
        target.addProperty("regionInstanceId", regionInstanceId);
        copyIfPresent(encoded, target, "test");
        copyIfPresent(encoded, target, "rootSelector");
        copyIfPresent(encoded, target, "targetMethod");
        if (hasRootCallId) {
            target.addProperty("rootCallId", rootCallId);
        }
    }

    public static final class Goal {
        private final RegionInstancePlan plan;
        private final JsonObject encoded;
        private final String goalId;
        private final String admissionState;
        private final GoalKind kind;
        private OutputClosureContract outputClosure;

        private Goal(RegionInstancePlan plan, JsonObject encoded) {
            this.plan = plan;
            this.encoded = encoded;
            goalId = string(encoded, "goalId");
            if (goalId.isEmpty()) {
                throw new IllegalArgumentException(
                        "closure goal ids must be nonempty and unique for "
                                + plan.regionInstanceId);
            }
            try {
                kind = GoalKind.valueOf(string(encoded, "kind"));
            } catch (RuntimeException invalid) {
                throw new IllegalArgumentException(
                        "goal kind must be OUTPUT_RELATION_CLOSURE or "
                                + "TARGET_REACH_CLOSURE");
            }
            admissionState = string(object(encoded, "admission"), "state");
        }

        public RegionInstancePlan plan() {
            return plan;
        }

        public String goalId() {
            return goalId;
        }

        public GoalKind kind() {
            return kind;
        }

        public boolean replayable() {
            return "READY".equals(admissionState)
                    || "DISCOVERED".equals(admissionState)
                    || "EXECUTABLE".equals(admissionState);
        }

        public Set<String> runtimeDefinitionMethods() {
            JsonElement definitions = encoded.get(
                    "runtimeDefinitionMethods");
            if (definitions == null || !definitions.isJsonArray()) {
                throw new IllegalArgumentException(
                        "closure goal requires runtimeDefinitionMethods array: "
                                + plan.regionInstanceId);
            }
            Set<String> methods = new LinkedHashSet<>();
            for (JsonElement method : definitions.getAsJsonArray()) {
                if (!method.isJsonPrimitive()
                        || !method.getAsJsonPrimitive().isString()
                        || method.getAsString().trim().isEmpty()) {
                    throw new IllegalArgumentException(
                            "runtimeDefinitionMethods must contain nonempty "
                                    + "strings: " + plan.regionInstanceId);
                }
                methods.add(method.getAsString().trim());
            }
            return methods;
        }

        public OutputClosureContract outputClosure() {
            if (!encoded.has(OutputClosureContract.FIELD)) {
                return null;
            }
            if (outputClosure != null) {
                return outputClosure;
            }
            outputClosure = OutputClosureCodec.decode(encoded);
            OutputClosureContract.Producer producer =
                    outputClosure.producer();
            if (!plan.regionId.equals(producer.regionId())
                    || !plan.regionInstanceId.equals(
                    producer.regionInstanceId())
                    || plan.hasRootCallId
                    && plan.rootCallId != producer.rootCallId()) {
                throw new IllegalArgumentException(
                        "outputClosure producer conflicts with artifact scope");
            }
            return outputClosure;
        }

        public void rejectOutputClosure() {
            if (encoded.has(OutputClosureContract.FIELD)) {
                throw new IllegalArgumentException(
                        "outputClosure requires OUTPUT_RELATION_CLOSURE");
            }
        }

        public JsonArray symbolize() {
            return array(encoded, "symbolize");
        }

        public JsonArray branches() {
            return array(encoded, "branches");
        }

        public JsonArray containerElementFieldBindings() {
            return array(encoded, "containerElementFieldBindings");
        }

        public JsonArray edgeBindings() {
            return array(encoded, "edgeBindings");
        }

        void writeTaskPayloadTo(JsonObject target) {
            target.addProperty("goalId", goalId);
            copyIfPresent(encoded, target,
                    "containerElementFieldBindings");
            copyIfPresent(encoded, target, "heapStateBindings");
            copyIfPresent(encoded, target,
                    "mapValueElementFieldProjections");
            if (kind == GoalKind.OUTPUT_RELATION_CLOSURE) {
                OutputClosureContract contract = outputClosure();
                if (contract != null) {
                    target.add(OutputClosureContract.FIELD,
                            contract.toJson());
                }
            } else {
                rejectOutputClosure();
            }
        }
    }

    private static void copyIfPresent(JsonObject source, JsonObject target,
                                      String field) {
        if (source.has(field)) {
            target.add(field, source.get(field).deepCopy());
        }
    }
}
