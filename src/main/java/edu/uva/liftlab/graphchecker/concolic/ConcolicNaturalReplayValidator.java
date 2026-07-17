package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** Validates a replay in which only upstream inputs may be materialized. */
public final class ConcolicNaturalReplayValidator {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();

    private ConcolicNaturalReplayValidator() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        JsonObject report = validate(arguments);
        write(arguments.output, GSON.toJson(report) + System.lineSeparator());
        System.out.println(GSON.toJson(report));
        if (!bool(report, "valid", false)) System.exit(2);
    }

    static JsonObject validate(Arguments arguments) throws IOException {
        require(arguments.plan, "natural-propagation activation plan");
        require(arguments.results, "natural-propagation replay results");
        require(arguments.projectionManifest, "model projection manifest");
        JsonObject projection = readJson(arguments.projectionManifest);
        List<JsonObject> plan = readJsonl(arguments.plan);
        List<JsonObject> results = readJsonl(arguments.results);
        if (integer(projection, "schemaVersion", 1) == 2
                && array(projection, "producerGroups").size() > 0) {
            return validateProducerGroups(arguments, projection, plan,
                    results);
        }
        List<String> failures = new ArrayList<>();

        if (!bool(projection, "projectionComplete", false)
                || !bool(projection, "downstreamInjectionForbidden", false)
                || !bool(projection, "boundedProducerInstanceSetComplete",
                false)) {
            failures.add("PROJECTION_MANIFEST_IS_NOT_UPSTREAM_ONLY");
        }
        List<String> upstreamActivations = strings(array(projection,
                "upstreamReplayActivations"));
        Set<String> uniqueUpstreamActivations = new LinkedHashSet<>(
                upstreamActivations);
        int expectedProducerCount = integer(projection,
                "expectedBoundedProducerInstanceCount", -1);
        if (upstreamActivations.isEmpty()
                || uniqueUpstreamActivations.size()
                != upstreamActivations.size()
                || expectedProducerCount < 1
                || upstreamActivations.size() != expectedProducerCount
                || integer(projection, "boundedProducerInstanceCount", -1)
                != expectedProducerCount
                || integer(projection, "upstreamReplayActivationCount", -1)
                != expectedProducerCount) {
            failures.add("BOUNDED_UPSTREAM_ACTIVATION_SET_INVALID");
        }
        String targetActivation = string(projection,
                "targetObservationActivation");
        JsonObject targetPlan = find(plan, targetActivation);
        String producerSetId = string(projection,
                "boundedProducerInstanceSetId");
        int boundedPlanCount = 0;
        for (JsonObject row : plan) {
            if (!bool(row, "boundedProducerBroadcast", false)) continue;
            boundedPlanCount++;
            if (!uniqueUpstreamActivations.contains(string(row,
                    "activationId")) || !producerSetId.equals(string(row,
                    "boundedProducerInstanceSetId"))) {
                failures.add("PLAN_CONTAINS_PRODUCER_OUTSIDE_DECLARED_BOUND");
            }
        }
        if (producerSetId.isEmpty()
                || boundedPlanCount != expectedProducerCount
                || !producerSetId.equals(string(targetPlan,
                "boundedProducerInstanceSetId"))) {
            failures.add("PLAN_PRODUCER_BOUND_DOES_NOT_MATCH_MANIFEST");
        }
        int capturedSourceInstances = 0;
        int capturedSourceActivations = 0;
        JsonArray producerEvidence = array(projection,
                "boundedProducerInstances");
        for (JsonElement element : producerEvidence) {
            if (!element.isJsonObject()) continue;
            JsonObject member = element.getAsJsonObject();
            if (bool(member, "capturedSourceInstance", false)) {
                capturedSourceInstances++;
            }
            if (bool(member, "capturedSourceActivation", false)) {
                capturedSourceActivations++;
            }
        }
        if (producerEvidence.size() != expectedProducerCount
                || capturedSourceInstances != 1
                || capturedSourceActivations != 1) {
            failures.add("MANIFEST_PRODUCER_BOUND_LACKS_UNIQUE_SOURCE");
        }
        for (String activation : upstreamActivations) {
            JsonObject upstreamPlan = find(plan, activation);
            if (upstreamPlan.size() == 0) {
                failures.add("UPSTREAM_ACTIVATION_MISSING_FROM_PLAN:"
                        + activation);
            } else {
                if (!bool(upstreamPlan, "concreteReplayOnly", false)
                        || !bool(upstreamPlan,
                        "boundedProducerBroadcast", false)) {
                    failures.add("UPSTREAM_ACTIVATION_IS_NOT_BOUNDED_"
                            + "CONCRETE_REPLAY:" + activation);
                }
                if (array(upstreamPlan,
                        "replayMaterializations").size() != 0
                        || array(upstreamPlan,
                        "forcedBranches").size() != 0) {
                    failures.add("UPSTREAM_SHORTCUT_PRESENT_IN_PLAN:"
                            + activation);
                }
            }
        }
        if (targetPlan.size() == 0) failures.add(
                "TARGET_OBSERVER_MISSING_FROM_PLAN");
        if (!bool(targetPlan, "concreteReplayOnly", false)
                || !bool(targetPlan, "observationOnlyReplay", false)) {
            failures.add("TARGET_IS_NOT_CONCRETE_OBSERVATION_ONLY_REPLAY");
        }
        if (array(targetPlan, "modelAssignments").size() != 0) {
            failures.add("DOWNSTREAM_MODEL_ASSIGNMENT_PRESENT_IN_PLAN");
        }
        if (array(targetPlan, "replayMaterializations").size() != 0) {
            failures.add("DOWNSTREAM_REPLAY_MATERIALIZATION_PRESENT_IN_PLAN");
        }
        if (array(targetPlan, "forcedBranches").size() != 0) {
            failures.add("DOWNSTREAM_BRANCH_OVERRIDE_PRESENT_IN_PLAN");
        }

        JsonObject target = find(results, targetActivation);
        if (target.size() == 0) failures.add(
                "TARGET_OBSERVATION_RESULT_MISSING");

        int expectedAssignments = integer(projection,
                "upstreamModelAssignmentCount", -1);
        JsonArray manifestAssignments = array(projection,
                "upstreamModelAssignments");
        if (expectedAssignments < 0
                || manifestAssignments.size() != expectedAssignments) {
            failures.add("MANIFEST_UPSTREAM_ASSIGNMENT_DEFINITION_COUNT_"
                    + "MISMATCH");
        }
        for (int index = 0; index < upstreamActivations.size(); index++) {
            JsonObject upstreamPlan = find(plan,
                    upstreamActivations.get(index));
            if (upstreamPlan.size() > 0 && (expectedAssignments < 0
                    || array(upstreamPlan, "modelAssignments").size()
                    != expectedAssignments)) {
                failures.add("UPSTREAM_PLANNED_ASSIGNMENT_COUNT_MISMATCH:"
                        + upstreamActivations.get(index));
            }
            if (upstreamPlan.size() > 0) {
                validateProjectedPlan(projection, manifestAssignments,
                        upstreamPlan, upstreamActivations.get(index),
                        failures);
            }
        }
        int totalAppliedAssignments = 0;
        JsonArray upstreamValidation = new JsonArray();
        for (String activation : upstreamActivations) {
            JsonObject upstreamPlan = find(plan, activation);
            JsonObject upstream = find(results, activation);
            JsonObject validation = new JsonObject();
            validation.addProperty("activationId", activation);
            validation.addProperty("resultObserved", upstream.size() > 0);
            if (upstream.size() == 0) {
                failures.add("UPSTREAM_REPLAY_RESULT_MISSING:"
                        + activation);
                upstreamValidation.add(validation);
                continue;
            }
            if (!"CONCOLIC_REGION_RESULT".equals(string(upstream, "event"))) {
                failures.add("UPSTREAM_REGION_DID_NOT_EXECUTE:"
                        + activation);
            }
            if (!"CONCRETE_REPLAY_ONLY".equals(string(upstream,
                    "executionMode"))) {
                failures.add("UPSTREAM_REGION_USED_CONCOLIC_ENGINE:"
                        + activation);
            }
            if (!bool(upstream, "allModelAssignmentsApplied", false)) {
                failures.add("UPSTREAM_MODEL_WAS_NOT_FULLY_APPLIED:"
                        + activation);
            }
            validateUpstreamAssignmentEvidence(upstreamPlan, upstream,
                    activation, failures);
            int applied = array(upstream,
                    "modelAssignmentsApplied").size();
            totalAppliedAssignments += applied;
            validation.addProperty("modelAssignmentAppliedCount", applied);
            validation.addProperty("allModelAssignmentsApplied",
                    bool(upstream, "allModelAssignmentsApplied", false));
            if (expectedAssignments < 0 || applied != expectedAssignments) {
                failures.add("UPSTREAM_APPLIED_ASSIGNMENT_COUNT_MISMATCH:"
                        + activation);
            }
            if (array(upstream, "replayMaterializationsApplied").size() != 0) {
                failures.add("UPSTREAM_REFERENCE_RESULT_INJECTION_USED:"
                        + activation);
            }
            if (bool(upstream, "branchOverrideUsed", false)) {
                failures.add("UPSTREAM_BRANCH_OVERRIDE_USED:" + activation);
            }
            upstreamValidation.add(validation);
        }

        JsonObject targetMapping = new JsonObject();
        if (target.size() > 0) {
            if (!"CONCOLIC_REGION_RESULT".equals(string(target, "event"))) {
                failures.add("TARGET_REGION_DID_NOT_EXECUTE");
            }
            if (!"CONCRETE_REPLAY_ONLY".equals(string(target,
                    "executionMode"))) {
                failures.add("TARGET_REGION_USED_CONCOLIC_ENGINE");
            }
            if (array(target, "modelAssignmentsApplied").size() != 0) {
                failures.add("DOWNSTREAM_MODEL_ASSIGNMENT_APPLIED");
            }
            if (array(target, "replayMaterializationsApplied").size() != 0) {
                failures.add("DOWNSTREAM_REFERENCE_RESULT_INJECTION_APPLIED");
            }
            if (bool(target, "branchOverrideUsed", false)) {
                failures.add("DOWNSTREAM_BRANCH_OVERRIDE_USED");
            }
            for (JsonElement element : array(target, "branchMappings")) {
                if (element.isJsonObject()
                        && bool(element.getAsJsonObject(), "scheduledTarget",
                        false)) {
                    if (targetMapping.size() != 0) {
                        failures.add("MULTIPLE_SCHEDULED_TARGET_MAPPINGS");
                    }
                    targetMapping = element.getAsJsonObject();
                }
            }
            if (targetMapping.size() == 0) {
                failures.add("SCHEDULED_TARGET_BRANCH_NOT_OBSERVED");
            } else {
                if (!bool(targetMapping, "scheduledOutcomeMatched", false)) {
                    failures.add("TARGET_BRANCH_OUTCOME_DID_NOT_MATCH");
                }
                if (!"PASS".equals(string(targetMapping,
                        "replayValidation"))) {
                    failures.add("TARGET_BRANCH_REPLAY_VALIDATION_FAILED");
                }
                if (bool(targetMapping, "overrideApplied", false)) {
                    failures.add("TARGET_BRANCH_WAS_OVERRIDDEN");
                }
            }
            validateExceptions(array(target, "exceptionChain"),
                    arguments.expectedExceptions, failures);
        }

        // Fail even if an unexpected extra result used a reference-result
        // injection.  The final test must contain no downstream shortcut at
        // all, not merely none on the selected target row.
        int globalReplayCount = 0;
        int globalOverrideCount = 0;
        int undeclaredAppliedAssignments = 0;
        for (JsonObject result : results) {
            globalReplayCount += array(result,
                    "replayMaterializationsApplied").size();
            if (bool(result, "branchOverrideUsed", false)) {
                globalOverrideCount++;
            }
            String activation = string(result, "activationId");
            if (!uniqueUpstreamActivations.contains(activation)
                    && !targetActivation.equals(activation)) {
                undeclaredAppliedAssignments += array(result,
                        "modelAssignmentsApplied").size();
            }
        }
        int undeclaredPlannedAssignments = 0;
        for (JsonObject row : plan) {
            String activation = string(row, "activationId");
            if (!uniqueUpstreamActivations.contains(activation)
                    && !targetActivation.equals(activation)) {
                undeclaredPlannedAssignments += array(row,
                        "modelAssignments").size();
            }
        }
        if (globalReplayCount != 0) failures.add(
                "REPLAY_MATERIALIZATION_APPEARED_IN_RESULT_SET");
        if (globalOverrideCount != 0) failures.add(
                "BRANCH_OVERRIDE_APPEARED_IN_RESULT_SET");
        if (undeclaredAppliedAssignments != 0
                || undeclaredPlannedAssignments != 0) {
            failures.add("UNDECLARED_MODEL_ASSIGNMENT_PRESENT");
        }

        JsonObject report = new JsonObject();
        report.addProperty("schemaVersion", 1);
        report.addProperty("kind", "CONCOLIC_NATURAL_PROPAGATION_REPLAY");
        report.addProperty("valid", failures.isEmpty());
        report.addProperty("status", failures.isEmpty()
                ? "VALIDATED_NATURAL_UPSTREAM_PROPAGATION"
                : "NATURAL_PROPAGATION_REPLAY_REJECTED");
        report.add("upstreamActivations",
                GSON.toJsonTree(upstreamActivations));
        report.addProperty("boundedProducerInstanceCount",
                upstreamActivations.size());
        report.addProperty("targetObservationActivation", targetActivation);
        report.addProperty("upstreamModelAssignmentCount",
                expectedAssignments);
        report.addProperty("upstreamAppliedModelAssignmentCount",
                totalAppliedAssignments);
        report.addProperty("expectedTotalUpstreamModelAssignmentCount",
                expectedAssignments < 0 ? -1
                        : expectedAssignments * upstreamActivations.size());
        report.add("upstreamReplayValidations", upstreamValidation);
        report.addProperty("downstreamPlannedModelAssignmentCount",
                array(targetPlan, "modelAssignments").size());
        report.addProperty("downstreamPlannedReplayMaterializationCount",
                array(targetPlan, "replayMaterializations").size());
        report.addProperty("downstreamAppliedModelAssignmentCount",
                array(target, "modelAssignmentsApplied").size());
        report.addProperty("downstreamAppliedReplayMaterializationCount",
                array(target, "replayMaterializationsApplied").size());
        report.addProperty("globalAppliedReplayMaterializationCount",
                globalReplayCount);
        report.addProperty("globalBranchOverrideCount", globalOverrideCount);
        report.addProperty("targetBranchObserved", targetMapping.size() > 0);
        report.addProperty("targetBranchOutcomeMatched",
                bool(targetMapping, "scheduledOutcomeMatched", false));
        report.addProperty("targetExitKind", string(target, "exitKind"));
        report.add("targetExceptionChain",
                array(target, "exceptionChain").deepCopy());
        report.add("failures", GSON.toJsonTree(failures));
        report.addProperty("failureCount", failures.size());
        report.addProperty("downstreamInjectionUsed", globalReplayCount != 0
                || array(target, "modelAssignmentsApplied").size() != 0
                || undeclaredAppliedAssignments != 0
                || undeclaredPlannedAssignments != 0);
        report.addProperty("branchOverrideUsed", globalOverrideCount != 0);
        report.addProperty("naturalPropagationEstablished",
                failures.isEmpty());
        report.addProperty("authority",
                "BOUNDED_PRODUCER_SET_MODEL_APPLIED_PLUS_UNFORCED_"
                        + "DOWNSTREAM_OBSERVATION");
        return report;
    }

    private static JsonObject validateProducerGroups(Arguments arguments,
                                                      JsonObject projection,
                                                      List<JsonObject> plan,
                                                      List<JsonObject> results) {
        List<String> failures = new ArrayList<>();
        JsonArray groups = array(projection, "producerGroups");
        if (!bool(projection, "projectionComplete", false)
                || !bool(projection, "downstreamInjectionForbidden", false)
                || !bool(projection, "boundedProducerInstanceSetComplete",
                false)
                || !bool(projection, "allProducerGroupsComplete", false)
                || groups.size() < 2
                || integer(projection, "producerGroupCount", -1)
                != groups.size()) {
            failures.add("PROJECTION_MANIFEST_IS_NOT_COMPLETE_MULTI_GROUP_"
                    + "UPSTREAM_ONLY");
        }
        if (integer(projection, "finalModelSolverInvocationCount", -1) != 1
                || !"ONE_SHARED_COMPLETE_COMPOSED_SMT_MODEL".equals(string(
                projection, "modelScope"))
                || string(projection, "solverInputSha256").isEmpty()) {
            failures.add("PRODUCER_GROUPS_DO_NOT_SHARE_ONE_FINAL_SMT_MODEL");
        }

        Set<String> duplicatePlanIds = duplicateActivationIds(plan);
        Set<String> duplicateResultIds = duplicateActivationIds(results);
        if (!duplicatePlanIds.isEmpty()) failures.add(
                "PLAN_ACTIVATION_IDS_NOT_GLOBALLY_UNIQUE:"
                        + duplicatePlanIds);
        if (!duplicateResultIds.isEmpty()) failures.add(
                "RESULT_ACTIVATION_IDS_NOT_GLOBALLY_UNIQUE:"
                        + duplicateResultIds);

        Set<String> groupIds = new LinkedHashSet<>();
        Set<String> groupRegions = new LinkedHashSet<>();
        Set<String> producerSetIds = new LinkedHashSet<>();
        Set<String> allUpstream = new LinkedHashSet<>();
        List<String> flattened = new ArrayList<>();
        JsonArray groupReports = new JsonArray();
        JsonArray upstreamValidations = new JsonArray();
        int totalApplied = 0;
        int expectedTotalApplied = 0;
        int totalProducerCount = 0;
        int totalAssignmentDefinitions = 0;
        int targetMapStateGroups = 0;
        int lookupKeyProducerGroups = 0;

        for (JsonElement element : groups) {
            if (!element.isJsonObject()) {
                failures.add("NON_OBJECT_PRODUCER_GROUP");
                continue;
            }
            JsonObject group = element.getAsJsonObject();
            String groupId = string(group, "producerGroupId");
            String region = string(group, "upstreamRegion");
            String role = string(group, "projectionRole");
            String setId = string(group, "boundedProducerInstanceSetId");
            List<String> activations = strings(array(group,
                    "upstreamReplayActivations"));
            Set<String> unique = new LinkedHashSet<>(activations);
            int expectedProducers = integer(group,
                    "expectedBoundedProducerInstanceCount", -1);
            int assignmentCount = integer(group,
                    "upstreamModelAssignmentCount", -1);
            JsonArray manifestAssignments = array(group,
                    "upstreamModelAssignments");
            boolean identityComplete = !groupId.isEmpty()
                    && !region.isEmpty()
                    && !string(group, "selectedCaseId").isEmpty()
                    && !string(group,
                    "selectedCaseSourceSummaryId").isEmpty()
                    && !string(group, "upstreamRegionInstance").isEmpty()
                    && !string(group, "upstreamSourceActivation").isEmpty()
                    && !string(group,
                    "upstreamReplayActivation").isEmpty()
                    && object(group,
                    "upstreamPreMapProducerEvidence").size() > 0;
            if ("TARGET_MAP_STATE".equals(role)) {
                targetMapStateGroups++;
                if (string(group, "targetDynamicBindingId").isEmpty()
                        || string(group, "targetDynamicEntryKey").isEmpty()
                        || group.has("lookupKeyProducerSolverTerm")) {
                    failures.add("TARGET_MAP_STATE_PROJECTION_INVALID:"
                            + groupId);
                }
            } else if ("LOOKUP_KEY_PRODUCER".equals(role)) {
                lookupKeyProducerGroups++;
                if (string(group,
                        "lookupKeyProducerRawEngineSymbol").isEmpty()
                        || string(group,
                        "lookupKeyProducerSolverTerm").isEmpty()
                        || string(group,
                        "lookupKeyProducerSummaryEffectId").isEmpty()
                        || !"RUNTIME_CONFIRMED_VALUE_EQUALITY_TO_LOOKUP_KEY_"
                        .concat("SOURCE").equals(string(group,
                        "lookupKeyProducerAuthority"))
                        || object(group,
                        "lookupKeyProducerWitness").size() == 0
                        || group.has("targetDynamicBindingId")) {
                    failures.add("LOOKUP_KEY_PRODUCER_PROJECTION_INVALID:"
                            + groupId);
                }
            } else {
                failures.add("UNKNOWN_PRODUCER_GROUP_PROJECTION_ROLE:"
                        + groupId + ":" + role);
            }
            if (!bool(group, "complete", false) || !identityComplete
                    || !groupIds.add(groupId)
                    || !groupRegions.add(region)
                    || setId.isEmpty() || !producerSetIds.add(setId)) {
                failures.add("PRODUCER_GROUP_IDENTITY_OR_BOUND_INVALID:"
                        + groupId);
            }
            if (activations.isEmpty() || unique.size() != activations.size()
                    || expectedProducers < 1
                    || activations.size() != expectedProducers
                    || integer(group, "boundedProducerInstanceCount", -1)
                    != expectedProducers
                    || integer(group, "upstreamReplayActivationCount", -1)
                    != expectedProducers
                    || assignmentCount < 0
                    || manifestAssignments.size()
                    != assignmentCount) {
                failures.add("PRODUCER_GROUP_CARDINALITY_INVALID:" + groupId);
            }
            for (String activation : activations) {
                flattened.add(activation);
                if (!allUpstream.add(activation)) {
                    failures.add("UPSTREAM_ACTIVATION_SHARED_ACROSS_GROUPS:"
                            + activation);
                }
            }

            int capturedInstances = 0;
            int capturedActivations = 0;
            Set<String> evidenceReplays = new LinkedHashSet<>();
            Set<String> evidenceInstances = new LinkedHashSet<>();
            JsonArray members = array(group, "boundedProducerInstances");
            for (JsonElement memberElement : members) {
                if (!memberElement.isJsonObject()) continue;
                JsonObject member = memberElement.getAsJsonObject();
                if (bool(member, "capturedSourceInstance", false)) {
                    capturedInstances++;
                }
                if (bool(member, "capturedSourceActivation", false)) {
                    capturedActivations++;
                }
                String replay = string(member, "replayActivationId");
                String instance = string(member, "regionInstanceId");
                if (replay.isEmpty() || !evidenceReplays.add(replay)
                        || instance.isEmpty()
                        || !evidenceInstances.add(instance)) {
                    failures.add("PRODUCER_GROUP_MEMBER_IDENTITY_INVALID:"
                            + groupId);
                }
            }
            if (members.size() != expectedProducers
                    || capturedInstances != 1 || capturedActivations != 1
                    || !evidenceReplays.equals(unique)) {
                failures.add("PRODUCER_GROUP_BOUND_LACKS_EXACT_SOURCE:"
                        + groupId);
            }

            JsonArray currentValidations = new JsonArray();
            for (String activation : activations) {
                JsonObject planned = find(plan, activation);
                if (planned.size() == 0) {
                    failures.add("UPSTREAM_ACTIVATION_MISSING_FROM_PLAN:"
                            + activation);
                } else {
                    if (!bool(planned, "concreteReplayOnly", false)
                            || !bool(planned, "boundedProducerBroadcast",
                            false)
                            || !groupId.equals(string(planned,
                            "producerGroupId"))
                            || !setId.equals(string(planned,
                            "boundedProducerInstanceSetId"))) {
                        failures.add("UPSTREAM_PLAN_CROSSES_GROUP_BOUNDARY:"
                                + activation);
                    }
                    if (array(planned, "modelAssignments").size()
                            != assignmentCount) {
                        failures.add("UPSTREAM_PLANNED_ASSIGNMENT_COUNT_"
                                + "MISMATCH:" + activation);
                    }
                    validateProjectedPlan(projection,
                            manifestAssignments, planned, activation,
                            failures);
                    if (array(planned,
                            "replayMaterializations").size() != 0
                            || array(planned, "forcedBranches").size() != 0) {
                        failures.add("UPSTREAM_SHORTCUT_PRESENT_IN_PLAN:"
                                + activation);
                    }
                }

                JsonObject observed = find(results, activation);
                JsonObject validation = new JsonObject();
                validation.addProperty("producerGroupId", groupId);
                validation.addProperty("activationId", activation);
                validation.addProperty("resultObserved", observed.size() > 0);
                if (observed.size() == 0) {
                    failures.add("UPSTREAM_REPLAY_RESULT_MISSING:"
                            + activation);
                } else {
                    if (!"CONCOLIC_REGION_RESULT".equals(string(observed,
                            "event"))) {
                        failures.add("UPSTREAM_REGION_DID_NOT_EXECUTE:"
                                + activation);
                    }
                    if (!"CONCRETE_REPLAY_ONLY".equals(string(observed,
                            "executionMode"))) {
                        failures.add("UPSTREAM_REGION_USED_CONCOLIC_ENGINE:"
                                + activation);
                    }
                    if (!bool(observed, "allModelAssignmentsApplied", false)) {
                        failures.add("UPSTREAM_MODEL_WAS_NOT_FULLY_APPLIED:"
                                + activation);
                    }
                    validateUpstreamAssignmentEvidence(planned, observed,
                            activation, failures);
                    int applied = array(observed,
                            "modelAssignmentsApplied").size();
                    totalApplied += applied;
                    validation.addProperty("modelAssignmentAppliedCount",
                            applied);
                    if (applied != assignmentCount) {
                        failures.add("UPSTREAM_APPLIED_ASSIGNMENT_COUNT_"
                                + "MISMATCH:" + activation);
                    }
                    if (array(observed,
                            "replayMaterializationsApplied").size() != 0) {
                        failures.add("UPSTREAM_REFERENCE_RESULT_INJECTION_"
                                + "USED:" + activation);
                    }
                    if (bool(observed, "branchOverrideUsed", false)) {
                        failures.add("UPSTREAM_BRANCH_OVERRIDE_USED:"
                                + activation);
                    }
                }
                currentValidations.add(validation);
                upstreamValidations.add(validation.deepCopy());
            }
            totalProducerCount += activations.size();
            totalAssignmentDefinitions += Math.max(assignmentCount, 0);
            if (assignmentCount >= 0) {
                expectedTotalApplied += assignmentCount * activations.size();
            }
            JsonObject groupReport = new JsonObject();
            groupReport.addProperty("producerGroupId", groupId);
            groupReport.addProperty("upstreamRegion", region);
            groupReport.addProperty("projectionRole", role);
            groupReport.addProperty("boundedProducerInstanceSetId", setId);
            groupReport.addProperty("producerCount", activations.size());
            groupReport.addProperty("modelAssignmentCount", assignmentCount);
            groupReport.add("upstreamReplayValidations", currentValidations);
            groupReports.add(groupReport);
        }

        if (targetMapStateGroups != 1 || lookupKeyProducerGroups < 1) {
            failures.add("PRODUCER_GROUP_ROLE_CARDINALITY_INVALID:target="
                    + targetMapStateGroups + ":lookup="
                    + lookupKeyProducerGroups);
        }

        List<String> declaredFlattened = strings(array(projection,
                "upstreamReplayActivations"));
        if (!flattened.equals(declaredFlattened)
                || integer(projection, "upstreamReplayActivationCount", -1)
                != flattened.size()
                || integer(projection,
                "upstreamModelAssignmentDefinitionCount", -1)
                != totalAssignmentDefinitions
                || integer(projection,
                "expectedTotalUpstreamModelAssignmentCount", -1)
                != expectedTotalApplied) {
            failures.add("FLATTENED_PRODUCER_GROUP_TOTALS_INVALID");
        }

        String targetActivation = string(projection,
                "targetObservationActivation");
        JsonObject targetPlan = find(plan, targetActivation);
        JsonObject target = find(results, targetActivation);
        if (targetActivation.isEmpty() || targetPlan.size() == 0) {
            failures.add("TARGET_OBSERVER_MISSING_FROM_PLAN");
        }
        if (target.size() == 0) failures.add(
                "TARGET_OBSERVATION_RESULT_MISSING");
        if (!bool(targetPlan, "concreteReplayOnly", false)
                || !bool(targetPlan, "observationOnlyReplay", false)) {
            failures.add("TARGET_IS_NOT_CONCRETE_OBSERVATION_ONLY_REPLAY");
        }
        if (!producerSetIds.equals(new LinkedHashSet<>(strings(array(
                targetPlan, "boundedProducerInstanceSetIds"))))) {
            failures.add("TARGET_PRODUCER_GROUP_BOUNDS_DO_NOT_MATCH");
        }
        if (array(targetPlan, "modelAssignments").size() != 0) {
            failures.add("DOWNSTREAM_MODEL_ASSIGNMENT_PRESENT_IN_PLAN");
        }
        if (array(targetPlan, "replayMaterializations").size() != 0) {
            failures.add("DOWNSTREAM_REPLAY_MATERIALIZATION_PRESENT_IN_PLAN");
        }
        if (array(targetPlan, "forcedBranches").size() != 0) {
            failures.add("DOWNSTREAM_BRANCH_OVERRIDE_PRESENT_IN_PLAN");
        }

        JsonObject targetMapping = new JsonObject();
        if (target.size() > 0) {
            if (!"CONCOLIC_REGION_RESULT".equals(string(target, "event"))) {
                failures.add("TARGET_REGION_DID_NOT_EXECUTE");
            }
            if (!"CONCRETE_REPLAY_ONLY".equals(string(target,
                    "executionMode"))) {
                failures.add("TARGET_REGION_USED_CONCOLIC_ENGINE");
            }
            if (array(target, "modelAssignmentsApplied").size() != 0) {
                failures.add("DOWNSTREAM_MODEL_ASSIGNMENT_APPLIED");
            }
            if (array(target,
                    "replayMaterializationsApplied").size() != 0) {
                failures.add("DOWNSTREAM_REFERENCE_RESULT_INJECTION_APPLIED");
            }
            if (bool(target, "branchOverrideUsed", false)) {
                failures.add("DOWNSTREAM_BRANCH_OVERRIDE_USED");
            }
            for (JsonElement element : array(target, "branchMappings")) {
                if (element.isJsonObject() && bool(element.getAsJsonObject(),
                        "scheduledTarget", false)) {
                    if (targetMapping.size() != 0) failures.add(
                            "MULTIPLE_SCHEDULED_TARGET_MAPPINGS");
                    targetMapping = element.getAsJsonObject();
                }
            }
            if (targetMapping.size() == 0) {
                failures.add("SCHEDULED_TARGET_BRANCH_NOT_OBSERVED");
            } else {
                if (!bool(targetMapping, "scheduledOutcomeMatched", false)) {
                    failures.add("TARGET_BRANCH_OUTCOME_DID_NOT_MATCH");
                }
                if (!"PASS".equals(string(targetMapping,
                        "replayValidation"))) {
                    failures.add("TARGET_BRANCH_REPLAY_VALIDATION_FAILED");
                }
                if (bool(targetMapping, "overrideApplied", false)) {
                    failures.add("TARGET_BRANCH_WAS_OVERRIDDEN");
                }
            }
            validateExceptions(array(target, "exceptionChain"),
                    arguments.expectedExceptions, failures);
        }

        int globalReplayCount = 0;
        int globalOverrideCount = 0;
        int undeclaredAppliedAssignments = 0;
        for (JsonObject result : results) {
            globalReplayCount += array(result,
                    "replayMaterializationsApplied").size();
            if (bool(result, "branchOverrideUsed", false)) {
                globalOverrideCount++;
            }
            String id = string(result, "activationId");
            if (!allUpstream.contains(id)) {
                undeclaredAppliedAssignments += array(result,
                        "modelAssignmentsApplied").size();
            }
        }
        int undeclaredPlannedAssignments = 0;
        int undeclaredPlanShortcuts = 0;
        for (JsonObject row : plan) {
            String id = string(row, "activationId");
            if (allUpstream.contains(id)) continue;
            undeclaredPlannedAssignments += array(row,
                    "modelAssignments").size();
            undeclaredPlanShortcuts += array(row,
                    "replayMaterializations").size();
            undeclaredPlanShortcuts += array(row, "forcedBranches").size();
        }
        if (globalReplayCount != 0) failures.add(
                "REPLAY_MATERIALIZATION_APPEARED_IN_RESULT_SET");
        if (globalOverrideCount != 0) failures.add(
                "BRANCH_OVERRIDE_APPEARED_IN_RESULT_SET");
        if (undeclaredAppliedAssignments != 0
                || undeclaredPlannedAssignments != 0
                || undeclaredPlanShortcuts != 0) {
            failures.add("DOWNSTREAM_OR_UNDECLARED_INJECTION_PRESENT");
        }

        JsonObject report = new JsonObject();
        report.addProperty("schemaVersion", 2);
        report.addProperty("kind", "CONCOLIC_NATURAL_PROPAGATION_REPLAY");
        report.addProperty("valid", failures.isEmpty());
        report.addProperty("status", failures.isEmpty()
                ? "VALIDATED_NATURAL_MULTI_GROUP_UPSTREAM_PROPAGATION"
                : "NATURAL_PROPAGATION_REPLAY_REJECTED");
        report.add("producerGroups", groupReports);
        report.addProperty("producerGroupCount", groups.size());
        report.add("upstreamActivations", GSON.toJsonTree(flattened));
        report.addProperty("boundedProducerInstanceCount",
                totalProducerCount);
        report.addProperty("upstreamModelAssignmentDefinitionCount",
                totalAssignmentDefinitions);
        report.addProperty("upstreamAppliedModelAssignmentCount",
                totalApplied);
        report.addProperty("expectedTotalUpstreamModelAssignmentCount",
                expectedTotalApplied);
        report.add("upstreamReplayValidations", upstreamValidations);
        report.addProperty("targetObservationActivation", targetActivation);
        report.addProperty("downstreamPlannedModelAssignmentCount",
                array(targetPlan, "modelAssignments").size());
        report.addProperty("downstreamAppliedModelAssignmentCount",
                array(target, "modelAssignmentsApplied").size());
        report.addProperty("globalAppliedReplayMaterializationCount",
                globalReplayCount);
        report.addProperty("globalBranchOverrideCount", globalOverrideCount);
        report.addProperty("targetBranchObserved", targetMapping.size() > 0);
        report.addProperty("targetBranchOutcomeMatched",
                bool(targetMapping, "scheduledOutcomeMatched", false));
        report.addProperty("targetExitKind", string(target, "exitKind"));
        report.add("targetExceptionChain",
                array(target, "exceptionChain").deepCopy());
        report.add("failures", GSON.toJsonTree(failures));
        report.addProperty("failureCount", failures.size());
        report.addProperty("downstreamInjectionUsed", globalReplayCount != 0
                || undeclaredAppliedAssignments != 0
                || undeclaredPlannedAssignments != 0
                || undeclaredPlanShortcuts != 0);
        report.addProperty("branchOverrideUsed", globalOverrideCount != 0);
        report.addProperty("naturalPropagationEstablished",
                failures.isEmpty());
        report.addProperty("authority",
                "MULTI_GROUP_BOUNDED_PRODUCER_MODELS_FROM_ONE_SMT_MODEL_"
                        + "PLUS_UNFORCED_DOWNSTREAM_OBSERVATION");
        return report;
    }

    /**
     * Natural propagation does not trust the aggregate applied-count flag.
     * It reuses the ordinary replay assignment admission boundary and, for a
     * keyed Map-view projection, requires the runtime's post-application
     * same-run key/order and output-identity evidence.
     */
    private static void validateUpstreamAssignmentEvidence(
            JsonObject planned, JsonObject observed, String activationId,
            List<String> failures) {
        if (array(observed, "unresolvedInputs").size() != 0) {
            failures.add("UPSTREAM_UNRESOLVED_INPUTS_PRESENT:"
                    + activationId);
        }
        List<String> assignmentProblems =
                ConcolicReplayValidator.validateDynamicAssignmentsForReplay(
                        array(planned, "modelAssignments"),
                        array(observed, "modelAssignmentsApplied"),
                        activationId);
        for (String problem : assignmentProblems) {
            failures.add("UPSTREAM_ASSIGNMENT_IDENTITY_INVALID:"
                    + activationId + ":" + problem);
        }

        Map<String, Integer> keyedGroups = new LinkedHashMap<>();
        for (JsonElement element : array(planned, "modelAssignments")) {
            if (!element.isJsonObject()) continue;
            JsonObject selector = object(element.getAsJsonObject(),
                    "mapProjectionSelector");
            if (selector.size() == 0) continue;
            String group = mapProjectionGroup(selector);
            Integer count = keyedGroups.get(group);
            keyedGroups.put(group, count == null ? 1 : count + 1);
        }
        if (keyedGroups.isEmpty()) return;

        JsonArray observations = array(observed,
                "mapValueElementProjectionObservations");
        for (Map.Entry<String, Integer> expected : keyedGroups.entrySet()) {
            List<JsonObject> entries = new ArrayList<>();
            List<JsonObject> outputs = new ArrayList<>();
            for (JsonElement element : observations) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject();
                if (!expected.getKey().equals(string(row, "groupId"))) {
                    continue;
                }
                if ("ENTRY_SNAPSHOT".equals(string(row, "phase"))) {
                    entries.add(row);
                } else if ("OUTPUT_IDENTITY_VALIDATION".equals(
                        string(row, "phase"))) {
                    outputs.add(row);
                }
            }
            if (entries.size() != 1 || outputs.size() != 1) {
                failures.add("UPSTREAM_MAP_PROJECTION_EVIDENCE_CARDINALITY_"
                        + "INVALID:" + activationId + ":"
                        + expected.getKey());
                continue;
            }
            JsonObject entry = entries.get(0);
            JsonObject output = outputs.get(0);
            boolean entryValid = bool(entry, "complete", false)
                    && bool(entry, "entrySnapshotComplete", false)
                    && bool(entry, "entrySetViewOrderVerified", false)
                    && bool(entry,
                    "expectedMapKeyAndSourceIndexValidated", false)
                    && expected.getValue() == integer(entry,
                    "expectedMapKeyAssignmentCount", -1)
                    && expected.getValue() == integer(entry,
                    "expectedMapKeyValidatedCount", -1)
                    && activationId.equals(string(entry,
                    "objectTokenScope"))
                    && "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                    .concat("POSITIONAL_REFERENCE_EQUALITY").equals(
                            string(entry, "entrySetViewOrderAuthority"));
            boolean outputValid = bool(output, "complete", false)
                    && bool(output, "outputIdentityVerified", false)
                    && longInteger(output,
                    "outputArrayObjectToken", 0L) > 0L
                    && exactMapProjectionOutputAuthority(string(output,
                    "outputVerificationAuthority"))
                    && activationId.equals(string(output,
                    "objectTokenScope"));
            if (!entryValid) failures.add(
                    "UPSTREAM_MAP_PROJECTION_KEY_ORDER_NOT_VALIDATED:"
                            + activationId + ":" + expected.getKey());
            if (!outputValid) failures.add(
                    "UPSTREAM_MAP_PROJECTION_OUTPUT_IDENTITY_NOT_VALIDATED:"
                            + activationId + ":" + expected.getKey());
        }
    }

    private static void validateProjectedPlan(
            JsonObject projection, JsonArray manifestAssignments,
            JsonObject planned, String activationId,
            List<String> failures) {
        for (String problem
                : ConcolicReplayValidator
                .validateProjectedAssignmentDefinitions(
                        manifestAssignments,
                        array(planned, "modelAssignments"))) {
            failures.add("UPSTREAM_MANIFEST_PLAN_ASSIGNMENT_MISMATCH:"
                    + activationId + ":" + problem);
        }
        String solverHash = string(projection, "solverInputSha256");
        String modelScope = string(projection, "modelScope");
        int schema = integer(projection, "schemaVersion", 1);
        if (!"Z3_BOUNDED_COMPOSITION_WITH_MATERIALIZABILITY_REFINEMENT"
                .equals(string(planned, "modelProjectionAuthority"))
                || solverHash.isEmpty()
                || !solverHash.equals(string(planned,
                "modelProjectionSolverInputSha256"))
                || !"ONE_SHARED_COMPLETE_COMPOSED_SMT_MODEL".equals(
                modelScope)
                || !modelScope.equals(string(planned,
                "modelProjectionModelScope"))
                || schema != integer(planned,
                "modelProjectionManifestSchemaVersion", -1)) {
            failures.add("UPSTREAM_MODEL_PROVENANCE_MISMATCH:"
                    + activationId);
        }
    }

    private static String mapProjectionGroup(JsonObject selector) {
        return string(selector, "mapInputPort") + "\n"
                + string(selector, "outputPort") + "\n"
                + string(selector, "outputCell") + "\n"
                + string(selector, "mapProjectionOperation");
    }

    private static boolean exactMapProjectionOutputAuthority(
            String authority) {
        return "ACTIVE_REGION_ROOT_RETURN_EXACT_PROJECTED_FIELD".equals(
                authority)
                || "ACTIVE_TOKEN_EXACT_ORIGINAL_CALL_ARGUMENT".equals(
                authority)
                || "ACTIVE_TOKEN_EXACT_POST_INSTANCE_FIELD_ASSIGNMENT"
                .equals(authority);
    }

    private static Set<String> duplicateActivationIds(
            List<JsonObject> rows) {
        Set<String> seen = new LinkedHashSet<>();
        Set<String> duplicates = new LinkedHashSet<>();
        for (JsonObject row : rows) {
            String id = string(row, "activationId");
            if (id.isEmpty() || !seen.add(id)) duplicates.add(id);
        }
        return duplicates;
    }

    private static void validateExceptions(JsonArray chain,
                                           List<String> expected,
                                           List<String> failures) {
        if (expected.isEmpty()) {
            if (chain.size() == 0) failures.add(
                    "TARGET_EXCEPTION_CHAIN_NOT_OBSERVED");
            return;
        }
        int cursor = 0;
        for (JsonElement element : chain) {
            if (!element.isJsonObject() || cursor >= expected.size()) continue;
            if (expected.get(cursor).equals(string(element.getAsJsonObject(),
                    "type"))) cursor++;
        }
        if (cursor != expected.size()) {
            failures.add("EXPECTED_TARGET_EXCEPTION_CHAIN_NOT_OBSERVED");
        }
    }

    private static JsonObject find(List<JsonObject> rows,
                                   String activationId) {
        JsonObject selected = new JsonObject();
        for (JsonObject row : rows) {
            if (!activationId.equals(string(row, "activationId"))) continue;
            if (selected.size() != 0) return new JsonObject();
            selected = row;
        }
        return selected;
    }

    private static void require(Path path, String label) throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            throw new IOException(label + " not found: " + path);
        }
    }

    private static JsonObject readJson(Path path) throws IOException {
        JsonElement parsed = new JsonParser().parse(new String(
                Files.readAllBytes(path), StandardCharsets.UTF_8));
        if (!parsed.isJsonObject()) throw new IOException(
                "Expected JSON object in " + path);
        return parsed.getAsJsonObject();
    }

    private static List<JsonObject> readJsonl(Path path) throws IOException {
        List<JsonObject> result = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) continue;
                JsonElement parsed = new JsonParser().parse(line);
                if (parsed.isJsonObject()) result.add(parsed.getAsJsonObject());
            }
        }
        return result;
    }

    private static void write(Path path, String value) throws IOException {
        Path parent = path.toAbsolutePath().getParent();
        if (parent != null) Files.createDirectories(parent);
        Files.write(path, value.getBytes(StandardCharsets.UTF_8),
                StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING);
    }

    private static JsonArray array(JsonObject object, String member) {
        JsonElement value = object == null ? null : object.get(member);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static JsonObject object(JsonObject object, String member) {
        JsonElement value = object == null ? null : object.get(member);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static List<String> strings(JsonArray values) {
        List<String> result = new ArrayList<>();
        for (JsonElement value : values) {
            if (value.isJsonPrimitive()) result.add(value.getAsString());
        }
        return result;
    }

    private static String string(JsonObject object, String member) {
        JsonElement value = object == null ? null : object.get(member);
        return value == null || value.isJsonNull() ? "" : value.getAsString();
    }

    private static int integer(JsonObject object, String member,
                               int fallback) {
        try {
            JsonElement value = object == null ? null : object.get(member);
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long longInteger(JsonObject object, String member,
                                    long fallback) {
        try {
            JsonElement value = object == null ? null : object.get(member);
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsLong();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static boolean bool(JsonObject object, String member,
                                boolean fallback) {
        try {
            JsonElement value = object == null ? null : object.get(member);
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    static final class Arguments {
        private Path plan;
        private Path results;
        private Path projectionManifest;
        private Path output;
        private final List<String> expectedExceptions = new ArrayList<>();

        static Arguments parse(String[] argv) {
            Arguments result = new Arguments();
            Map<String, String> values = new LinkedHashMap<>();
            for (int index = 0; index < argv.length; index++) {
                String argument = argv[index];
                if (!argument.startsWith("--") || index + 1 >= argv.length) {
                    throw new IllegalArgumentException("Expected --key value, "
                            + "got " + argument);
                }
                String key = argument.substring(2);
                String value = argv[++index];
                if ("expected-exception".equals(key)) {
                    result.expectedExceptions.add(value);
                } else {
                    values.put(key, value);
                }
            }
            result.plan = path(values, "plan");
            result.results = path(values, "results");
            result.projectionManifest = path(values,
                    "projection-manifest");
            result.output = path(values, "output");
            return result;
        }

        private static Path path(Map<String, String> values, String key) {
            String value = values.get(key);
            if (value == null || value.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --" + key);
            }
            return Paths.get(value);
        }
    }
}
