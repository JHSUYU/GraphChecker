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
public final class RegionInstancePlan extends PlanRow {
    /** Task members the runtime stamped on one coarse region occurrence, in a
     *  fixed order.  A field with no direct evidence stays absent. */
    private static final String[] OCCURRENCE_FIELDS = {
            // The recorded root call this occurrence ran in.
            "activationId",
            // Exact dynamic executions of configured-source hook sites in
            // this coarse occurrence.
            ConfiguredSourcePhaseContract.PLAN_FIELD,
            // Declared communication ports this occurrence exports/attaches.
            CommunicationHandoffSpec.FIELD,
            edu.uva.liftlab.graphchecker.concolic.BoundedLoopComposition
                    .PLAN_FIELD
    };
    private final List<Goal> goals;
    private final Set<String> demandedByRegionIds;

    private RegionInstancePlan(JsonObject source) {
        super(source, "region plan", true);
        Set<String> consumers = new LinkedHashSet<>();
        for (JsonElement element : array(encoded, "demandedByRegionIds")) {
            if (element.isJsonPrimitive()
                    && !element.getAsString().isEmpty()) {
                consumers.add(element.getAsString());
            }
        }
        demandedByRegionIds = Collections.unmodifiableSet(consumers);
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
        // README REGION-1: one local occurrence is one coarse task and one
        // guarded summary.  Bounded write versions of one port belong inside
        // the single closure, not in a second goal.
        if (decoded.size() != 1) {
            throw new IllegalArgumentException(
                    "region occurrence requires exactly one closure goal, "
                            + "found " + decoded.size() + ": "
                            + occurrenceId());
        }
        goals = Collections.unmodifiableList(decoded);
    }

    public static RegionInstancePlan decode(JsonObject encoded) {
        if (encoded == null) {
            throw new IllegalArgumentException("region plan is required");
        }
        return new RegionInstancePlan(encoded.deepCopy());
    }

    public List<Goal> goals() { return goals; }

    /** The consumer regions a shared-location admission serves. */
    public Set<String> demandedByRegionIds() { return demandedByRegionIds; }

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
        // The once-only-root rule travels to the task row under the names the
        // region row published: instrumentation and the runtime see the task,
        // never the region plan it came from.
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
            try {
                kind = ClosureGoalKind.fromGoal(encoded);
            } catch (RuntimeException invalid) {
                throw new IllegalArgumentException("goal kind must be one of "
                        + java.util.Arrays.toString(
                        ClosureGoalKind.values()), invalid);
            }
            runtimeDefinitionMethods = decodeRuntimeDefinitionMethods();
        }

        public RegionInstancePlan plan() { return plan; }

        public String goalId() { return string(encoded, "goalId"); }

        public ClosureGoalKind kind() { return kind; }

        public boolean replayable() {
            return "READY".equals(admissionState());
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

        public JsonArray symbolize() {
            return array(encoded, "symbolize").deepCopy();
        }

        public JsonArray branches() {
            return array(encoded, "branches").deepCopy();
        }

        public JsonArray edgeBindings() {
            return array(encoded, "edgeBindings").deepCopy();
        }

        void writeTaskPayloadTo(JsonObject target) {
            target.addProperty("goalId", goalId());
            copyIfPresent(encoded, target, ExecutionTask.REPLAY_ENTRY);
            // Carrier declarations are the planner's and only the replay can
            // act on them.  An absent member stays absent: inventing one would
            // version a location the target slice never asked about.
            JsonArray carriers =
                    array(encoded, ExecutionTask.SHARED_CARRIERS);
            if (carriers.size() > 0) {
                target.add(ExecutionTask.SHARED_CARRIERS,
                        carriers.deepCopy());
            }
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
