package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Execution goals for one causal-skeleton region occurrence. */
public final class RegionInstancePlan {
    /**
     * Task members the runtime stamped on one coarse region occurrence, in a
     * fixed order.  A field with no direct evidence stays absent, never
     * defaulted.
     */
    private static final String[] OCCURRENCE_FIELDS = {
            // The recorded root call this occurrence ran in.  Carried
            // explicitly because a task has no other route to it: the
            // identity block writes sourceKey/occurrenceId/relationKey/
            // regionId and no traceEvidence, and an activationId is a
            // different shape from an occurrenceId.
            "activationId",
            // Exact dynamic executions of configured-source publish/consume
            // hook sites inside this coarse occurrence.  A scheduler may split
            // logical source versions by these phases without changing the
            // replay root identity.
            ConfiguredSourcePhaseContract.PLAN_FIELD,
            // The declared communication ports this occurrence exports or
            // attaches, with the site each is handed to the VM at.
            CommunicationHandoffSpec.FIELD,
            edu.uva.liftlab.graphchecker.concolic.BoundedLoopComposition
                    .PLAN_FIELD
    };
    private final JsonObject encoded;
    private final List<Goal> goals;

    private RegionInstancePlan(JsonObject source) {
        encoded = source.deepCopy();
        require(sourceKey(), "sourceKey");
        require(occurrenceId(), "occurrenceId");
        require(relationKey(), "relationKey");
        require(regionId(), "regionId");
        for (ConfiguredSourcePhaseContract.Occurrence phase
                : ConfiguredSourcePhaseContract.occurrencesOf(
                encoded.get(ConfiguredSourcePhaseContract.PLAN_FIELD), true)) {
            if (!occurrenceId().equals(phase.sourceOccurrenceId())) {
                throw new IllegalArgumentException(
                        "configured source phase belongs to another "
                                + "occurrence: " + phase.phaseId());
            }
        }

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
        if (decoded.isEmpty()) {
            throw new IllegalArgumentException(
                    "region occurrence requires at least one closure goal: "
                            + occurrenceId());
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

    /**
     * Read-only view for whole-plan indexing.  Callers must not mutate it.
     * Large runtime plans are immutable after decoding; copying the complete
     * output closure for every target-ranking pass is pure overhead.
     */
    public JsonObject jsonView() { return encoded; }

    public String sourceKey() { return string(encoded, "sourceKey"); }

    public String occurrenceId() { return string(encoded, "occurrenceId"); }

    public String relationKey() { return string(encoded, "relationKey"); }

    public String regionId() { return string(encoded, "regionId"); }

    /**
     * The identity one plan row is unique under.
     *
     * <p>A region is coarse - one selected execution-context entry and the
     * selected nested calls executed in it - so one region occurrence is one
     * plan row, and the occurrence alone is that identity.</p>
     */
    public String occurrenceKey() {
        return occurrenceId();
    }

    public boolean containsOccurrence(String candidate) {
        return occurrenceId().equals(candidate == null ? ""
                : candidate.trim());
    }

    public List<Goal> goals() { return goals; }

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
            require(goalId(), "goalId");
            try {
                kind = ClosureGoalKind.fromGoal(encoded);
            } catch (RuntimeException invalid) {
                throw new IllegalArgumentException("goal kind must be one of "
                        + java.util.Arrays.toString(
                        ClosureGoalKind.values()), invalid);
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

        /** Read-only traversal view for target/producer graph discovery. */
        public JsonArray symbolizeView() {
            return array(encoded, "symbolize");
        }

        public JsonArray branches() {
            return array(encoded, "branches").deepCopy();
        }

        /** Read-only traversal view for target ranking and guard counting. */
        public JsonArray branchesView() {
            return array(encoded, "branches");
        }

        public JsonArray edgeBindings() {
            return array(encoded, "edgeBindings").deepCopy();
        }

        /**
         * Read-only traversal view for graph discovery.  The canonical plan
         * owns this array; callers must copy individual rows before storing
         * or changing them.  Avoiding a deep copy here matters because one
         * bounded supergraph can contain the same edge ledger on hundreds of
         * occurrence goals.
         */
        public JsonArray edgeBindingsView() {
            return array(encoded, "edgeBindings");
        }

        /** Shared locations this goal asks its replay to select as carriers. */
        public JsonArray sharedCarriers() {
            return array(encoded, ExecutionTask.SHARED_CARRIERS).deepCopy();
        }

        void writeTaskIdentityTo(JsonObject target) {
            plan.writeTaskIdentityTo(target);
        }

        void writeTaskPayloadTo(JsonObject target) {
            target.addProperty("goalId", goalId());
            copyIfPresent(encoded, target, ExecutionTask.REPLAY_ENTRY);
            if (outputClosure != null) {
                target.add(OutputClosureContract.FIELD,
                        outputClosure.toJson());
            }
            // Carrier declarations are the planner's, and only the replay can
            // act on them, so they pass through untouched.  An absent member
            // stays absent: a task that declares no carrier selects none, and
            // inventing one here would version a location the target slice
            // never asked about.
            JsonArray carriers = sharedCarriers();
            if (carriers.size() > 0) {
                target.add(ExecutionTask.SHARED_CARRIERS, carriers);
            }
        }

        private OutputClosureContract decodeOutputClosure() {
            OutputClosureContract contract = OutputClosureCodec.decode(encoded);
            OutputClosureContract.Producer producer = contract.producer();
            if (!plan.regionId().equals(producer.regionId())
                    || !plan.relationKey().equals(producer.relationKey())) {
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
