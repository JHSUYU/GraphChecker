package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan.Goal;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Discovers the producer and target campaigns in one runtime region plan.
 *
 * <p>Producer position is graph-relative: a producer may supply another
 * producer or the target.  Field names and graph depth therefore never become
 * workflow identities.</p>
 */
public final class RuntimeWorkflowDiscovery {
    private static final Pattern CALL_ID = Pattern.compile(
            "(?:^|[#@])call([0-9]+)(?:$|[^0-9])");
    private static final Pattern GOAL_DIGEST = Pattern.compile(
            "(?i)([0-9a-f]{8,})$");

    private final List<RegionInstancePlan> plans = new ArrayList<>();
    private final List<Demand> demands;
    private final Target target;

    private RuntimeWorkflowDiscovery(Path regionPlan) throws IOException {
        Set<String> instances = new LinkedHashSet<>();
        for (JsonObject row : ArtifactIO.readJsonl(regionPlan)) {
            RegionInstancePlan plan = RegionInstancePlan.decode(row);
            if (!instances.add(plan.regionInstanceId())) {
                throw new IOException("duplicate regionInstanceId: "
                        + plan.regionInstanceId());
            }
            plans.add(plan);
        }
        if (plans.isEmpty()) {
            throw new IOException("runtime region plan is empty");
        }
        target = discoverTarget();
        demands = discoverDemands();
    }

    public static void main(String[] argv) throws Exception {
        Map<String, String> args = parseArgs(argv);
        String command = required(args, "command");
        RuntimeWorkflowDiscovery discovery = new RuntimeWorkflowDiscovery(
                Paths.get(required(args, "region-plan")));
        switch (command) {
            case "discover":
                discovery.printDiscovery();
                return;
            case "producer-demands":
                for (Demand demand : discovery.demands) {
                    System.out.println(demand.campaignId);
                }
                return;
            case "producer-binding": {
                Demand demand = discovery.demand(
                        required(args, "campaign"));
                System.out.println(demand.binding());
                return;
            }
            case "target-binding":
                System.out.println(discovery.target.binding());
                return;
            case "scheduled-task":
                System.out.println(discovery.scheduledProducerTask(
                        required(args, "campaign"),
                        Paths.get(required(args, "task-plan"))));
                return;
            case "scheduled-target-task":
                System.out.println(discovery.scheduledTargetTask(
                        Paths.get(required(args, "task-plan"))));
                return;
            default:
                throw new IllegalArgumentException(
                        "unknown discovery command: " + command);
        }
    }

    /**
     * Selects every READY producer goal in the reverse runtime read-from
     * closure rooted at the unique target instance.
     */
    private List<Demand> discoverDemands() throws IOException {
        List<Demand> candidates = new ArrayList<>();
        for (RegionInstancePlan plan : plans) {
            for (Goal goal : plan.goals()) {
                if (!goal.kind().capturesOutputRelation()) {
                    continue;
                }
                List<JsonObject> edges = trustedEdges(goal);
                if (!edges.isEmpty()) {
                    candidates.add(new Demand(plan, goal, edges));
                }
            }
        }

        Set<String> reachedInstances = new LinkedHashSet<>();
        reachedInstances.add(target.regionInstanceId);
        Set<Demand> selected = new LinkedHashSet<>();
        boolean changed;
        do {
            changed = false;
            for (Demand demand : candidates) {
                if (selected.contains(demand)
                        || !demand.feedsAny(reachedInstances)) {
                    continue;
                }
                requireReady(demand);
                selected.add(demand);
                reachedInstances.add(demand.regionInstanceId);
                changed = true;
            }
        } while (changed);

        if (selected.isEmpty()) {
            throw new IOException("runtime read-from graph has no executable "
                    + "producer path to target; targetRegion="
                    + target.regionId + "; targetInstance="
                    + target.regionInstanceId + "; outputGoals="
                    + outputGoalAdmissions());
        }

        List<Demand> result = new ArrayList<>(selected);
        result.sort(Comparator.comparing(Demand::sortKey));
        Set<String> campaignIds = new LinkedHashSet<>();
        for (Demand demand : result) {
            if (!campaignIds.add(demand.campaignId)) {
                throw new IOException("duplicate producer campaignId: "
                        + demand.campaignId);
            }
        }
        return result;
    }

    private Target discoverTarget() throws IOException {
        List<Target> matches = new ArrayList<>();
        for (RegionInstancePlan plan : plans) {
            for (Goal goal : plan.goals()) {
                if (goal.kind() == ClosureGoalKind.TARGET_REACH_CLOSURE) {
                    matches.add(new Target(plan, goal));
                }
            }
        }
        if (matches.size() != 1) {
            throw new IOException("expected one target reach closure; found "
                    + matches.size());
        }
        Target result = matches.get(0);
        if (!result.goal.replayable()) {
            throw new IOException("target goal is not replayable; "
                    + result.context());
        }
        return result;
    }

    private static List<JsonObject> trustedEdges(Goal goal) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement item : goal.edgeBindings()) {
            if (item.isJsonObject()
                    && AutomaticRegionEdge.trustedRuntimeReadFromBinding(
                    item.getAsJsonObject())) {
                result.add(item.getAsJsonObject());
            }
        }
        return result;
    }

    private static void requireReady(Demand demand) throws IOException {
        if (!"READY".equals(demand.goal.admissionState())) {
            throw new IOException("producer goal on target dependency path "
                    + "is not READY; " + demand.context());
        }
        if (demand.goal.outputClosure() == null) {
            throw new IOException("READY producer goal has no outputClosure; "
                    + demand.context());
        }
    }

    private List<String> outputGoalAdmissions() {
        List<String> result = new ArrayList<>();
        for (RegionInstancePlan plan : plans) {
            for (Goal goal : plan.goals()) {
                if (goal.kind().capturesOutputRelation()) {
                    result.add(context(plan, goal));
                }
            }
        }
        return result;
    }

    private String scheduledProducerTask(String campaignId, Path taskPlan)
            throws IOException {
        Demand demand = demand(campaignId);
        List<String> matches = new ArrayList<>();
        for (JsonObject row : ArtifactIO.readJsonl(taskPlan)) {
            ExecutionTask task = ExecutionTask.decode(row);
            if (demand.regionId.equals(task.regionId())
                    && demand.regionInstanceId.equals(task.regionInstanceId())
                    && demand.goalId.equals(task.goalId())
                    && task.goalKind().capturesOutputRelation()
                    && task.outputClosure() != null) {
                matches.add(task.taskId());
            }
        }
        return only(matches, "scheduled producer task; "
                + demand.context());
    }

    private String scheduledTargetTask(Path taskPlan) throws IOException {
        List<String> matches = new ArrayList<>();
        for (JsonObject row : ArtifactIO.readJsonl(taskPlan)) {
            ExecutionTask task = ExecutionTask.decode(row);
            if (target.regionId.equals(task.regionId())
                    && target.regionInstanceId.equals(task.regionInstanceId())
                    && target.goalId.equals(task.goalId())
                    && task.goalKind().capturesTargetReach()) {
                matches.add(task.taskId());
            }
        }
        return only(matches, "scheduled target task; " + target.context());
    }

    private Demand demand(String campaignId) throws IOException {
        for (Demand demand : demands) {
            if (demand.campaignId.equals(campaignId)) {
                return demand;
            }
        }
        throw new IOException("unknown producer campaign: " + campaignId);
    }

    private void printDiscovery() {
        System.out.println("role\tcampaign\tregion\tinstance\tgoal");
        for (Demand demand : demands) {
            System.out.println("PRODUCER\t" + demand.binding());
        }
        System.out.println("TARGET\t" + target.binding());
    }

    private static String campaignId(String regionId,
                                     String regionInstanceId,
                                     String goalId) {
        String region = safeToken(regionId);
        Matcher call = CALL_ID.matcher(regionInstanceId);
        String invocation = call.find()
                ? "call" + call.group(1)
                : "instance-"
                + ArtifactIO.sha256(regionInstanceId).substring(0, 8);
        Matcher goalDigest = GOAL_DIGEST.matcher(goalId);
        String digest = goalDigest.find()
                ? goalDigest.group(1).substring(0, 8).toLowerCase()
                : ArtifactIO.sha256(goalId).substring(0, 8);
        return region + "-" + invocation + "-" + digest;
    }

    private static String safeToken(String value) {
        String token = value == null ? "" : value.trim()
                .replaceAll("[^A-Za-z0-9._-]+", "-")
                .replaceAll("^-+|-+$", "");
        return token.isEmpty() ? "region" : token;
    }

    private static String context(RegionInstancePlan plan, Goal goal) {
        return "region=" + plan.regionId()
                + "; instance=" + plan.regionInstanceId()
                + "; goal=" + goal.goalId()
                + "; admission=" + goal.admissionState()
                + "; blockers=" + goal.admissionBlockers();
    }

    private static String only(List<String> values, String subject)
            throws IOException {
        if (values.size() != 1) {
            throw new IOException("expected one " + subject + "; found "
                    + values.size());
        }
        return values.get(0);
    }

    private static String required(JsonObject object, String field)
            throws IOException {
        String value = string(object, field);
        if (value.isEmpty()) {
            throw new IOException("trusted runtime edge is missing " + field);
        }
        return value;
    }

    private static String required(Map<String, String> args, String name) {
        String value = args.get(name);
        if (value == null || value.trim().isEmpty()) {
            throw new IllegalArgumentException("--" + name
                    + " is required");
        }
        return value.trim();
    }

    private static Map<String, String> parseArgs(String[] argv) {
        Map<String, String> result = new LinkedHashMap<>();
        for (int index = 0; index < argv.length; index += 2) {
            if (!argv[index].startsWith("--") || index + 1 >= argv.length) {
                throw new IllegalArgumentException(
                        "arguments must be --name value pairs");
            }
            result.put(argv[index].substring(2), argv[index + 1]);
        }
        return result;
    }

    private static final class Demand {
        private final RegionInstancePlan plan;
        private final Goal goal;
        private final String campaignId;
        private final String regionId;
        private final String regionInstanceId;
        private final String goalId;
        private final List<JsonObject> edges;

        private Demand(RegionInstancePlan plan, Goal goal,
                       List<JsonObject> edges) {
            this.plan = plan;
            this.goal = goal;
            regionId = plan.regionId();
            regionInstanceId = plan.regionInstanceId();
            goalId = goal.goalId();
            campaignId = campaignId(regionId, regionInstanceId, goalId);
            this.edges = edges;
        }

        private boolean feedsAny(Set<String> downstreamInstances)
                throws IOException {
            for (JsonObject edge : edges) {
                if (downstreamInstances.contains(
                        required(edge, "toRegionInstance"))) {
                    return true;
                }
            }
            return false;
        }

        private String binding() {
            return campaignId + "\t" + regionId + "\t"
                    + regionInstanceId + "\t" + goalId;
        }

        private String context() {
            return RuntimeWorkflowDiscovery.context(plan, goal);
        }

        private String sortKey() {
            return regionInstanceId + "\n" + goalId;
        }
    }

    private static final class Target {
        private final RegionInstancePlan plan;
        private final Goal goal;
        private final String campaignId;
        private final String regionId;
        private final String regionInstanceId;
        private final String goalId;

        private Target(RegionInstancePlan plan, Goal goal) {
            this.plan = plan;
            this.goal = goal;
            regionId = plan.regionId();
            regionInstanceId = plan.regionInstanceId();
            goalId = goal.goalId();
            campaignId = campaignId(regionId, regionInstanceId, goalId);
        }

        private String binding() {
            return campaignId + "\t" + regionId + "\t"
                    + regionInstanceId + "\t" + goalId;
        }

        private String context() {
            return RuntimeWorkflowDiscovery.context(plan, goal);
        }
    }
}
