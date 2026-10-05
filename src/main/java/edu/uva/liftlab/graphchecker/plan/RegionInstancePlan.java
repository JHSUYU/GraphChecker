package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/** Execution goals for one causal-skeleton region occurrence. */
public final class RegionInstancePlan extends PlanRow {
    /** Occurrence members the runtime stamped, copied to the task; absent when
     *  unevidenced. */
    private static final String[] OCCURRENCE_FIELDS = {
            "activationId",
            ConfiguredSourcePhaseContract.PLAN_FIELD,
            CommunicationHandoffSpec.FIELD,
            LoopBoundPolicy.PLAN_FIELD,
            RuntimeSelectedRegionFinalizer.CONTEXT_SHAPE,
            RuntimeSelectedRegionFinalizer.RECORDED_BESIDE,
            DeclaredSiteCapture.ROOT_CALL_ID
    };
    private final Goal goal;

    private RegionInstancePlan(JsonObject source) {
        super(source, "region plan");
        List<Goal> decoded = new ArrayList<>();
        Set<String> ids = new LinkedHashSet<>();
        for (JsonElement element : array(encoded, "closureGoals")) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "closureGoals must contain objects for "
                                + occurrenceId());
            }
            Goal each = new Goal(this, element.getAsJsonObject());
            if (!ids.add(each.goalId())) {
                throw new IllegalArgumentException(
                        "closure goal ids must be unique for "
                                + occurrenceId());
            }
            decoded.add(each);
        }
        // One occurrence = one task = one guarded summary.
        if (decoded.size() != 1) {
            throw new IllegalArgumentException(
                    "region occurrence requires exactly one closure goal, "
                            + "found " + decoded.size() + ": "
                            + occurrenceId());
        }
        goal = decoded.get(0);
    }

    public static RegionInstancePlan decode(JsonObject encoded) {
        if (encoded == null) {
            throw new IllegalArgumentException("region plan is required");
        }
        return new RegionInstancePlan(encoded.deepCopy());
    }

    /** The occurrence's one closure goal. */
    public Goal goal() { return goal; }

    void writeTaskIdentityTo(JsonObject target) {
        target.addProperty("sourceKey", sourceKey());
        target.addProperty("occurrenceId", occurrenceId());
        target.addProperty("relationKey", relationKey());
        target.addProperty("regionId", regionId());
        for (String field : OCCURRENCE_FIELDS) {
            copyIfPresent(encoded, target, field);
        }
        copyIfPresent(encoded, target, "rootSelector");
        copyIfPresent(encoded, target, "targetMethod");
        // The task row, not the region plan, is what instrumentation and
        // runtime read.
        copyIfPresent(encoded, target, LoopBoundPolicy.ROOT_AUTHORITY);
        copyIfPresent(encoded, target, LoopBoundPolicy.ROOT_LOOP);
    }

    public static final class Goal {
        private final RegionInstancePlan plan;
        private final JsonObject encoded;
        private final ClosureGoalKind kind;
        private final Set<String> runtimeDefinitionMethods;

        private Goal(RegionInstancePlan plan, JsonObject source) {
            this.plan = plan;
            this.encoded = source.deepCopy();
            plan.require(goalId(), "goalId");
            kind = ClosureGoalKind.fromGoal(encoded);
            runtimeDefinitionMethods = decodeRuntimeDefinitionMethods();
        }

        public RegionInstancePlan plan() { return plan; }

        public String goalId() { return optionalString(encoded, "goalId"); }

        public ClosureGoalKind kind() { return kind; }

        public boolean replayable() {
            return "READY".equals(admissionState());
        }

        public String admissionState() {
            return optionalString(object(encoded, "admission"), "state");
        }

        public JsonArray admissionBlockers() {
            return array(object(encoded, "admission"), "blockers");
        }

        public Set<String> runtimeDefinitionMethods() {
            return runtimeDefinitionMethods;
        }

        public JsonArray symbolize() {
            return array(encoded, "symbolize").deepCopy();
        }

        public JsonArray branches() {
            return array(encoded, "branches").deepCopy();
        }

        void writeTaskPayloadTo(JsonObject target) {
            target.addProperty("goalId", goalId());
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
    }

    private static void copyIfPresent(
            JsonObject source, JsonObject target, String field) {
        if (source.has(field)) {
            target.add(field, source.get(field).deepCopy());
        }
    }
}
