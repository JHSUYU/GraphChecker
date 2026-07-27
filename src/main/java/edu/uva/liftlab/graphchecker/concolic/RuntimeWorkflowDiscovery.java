package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan.Goal;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Typed discovery boundary for the local shared-field workflow.
 *
 * <p>The fixture shell owns process orchestration only. This class owns
 * region-plan decoding, read-from channel grouping, target selection and
 * scheduled task selection.</p>
 */
public final class RuntimeWorkflowDiscovery {
    private static final Pattern FIELD_CELL = Pattern.compile(
            "^<[^:]+:\\s+\\S+\\s+([^ >]+)>$");

    private final List<RegionInstancePlan> plans;
    private final List<Channel> channels;
    private final List<Demand> demands;
    private final Target target;

    private RuntimeWorkflowDiscovery(Path regionPlan) throws IOException {
        plans = new ArrayList<>();
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
        channels = discoverChannels();
        demands = discoverDemands();
        target = discoverTarget();
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
            case "producer-channels":
                for (Demand demand : discovery.demands) {
                    System.out.println(demand.handle);
                }
                return;
            case "producer-binding":
                Demand demand = discovery.demand(
                        required(args, "channel"));
                System.out.println(demand.regionId + "\t"
                        + demand.regionInstanceId + "\t" + demand.goalId);
                return;
            case "target-binding":
                System.out.println(discovery.target.regionId + "\t"
                        + discovery.target.regionInstanceId + "\t"
                        + discovery.target.goalId);
                return;
            case "scheduled-task":
                System.out.println(discovery.scheduledProducerTask(
                        required(args, "channel"),
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

    private List<Channel> discoverChannels() throws IOException {
        List<JsonObject> validatedEdges = new ArrayList<>();
        for (RegionInstancePlan plan : plans) {
            for (Goal goal : plan.goals()) {
                if (!goal.kind().capturesOutputRelation()) continue;
                for (JsonElement item : goal.edgeBindings()) {
                    if (item.isJsonObject()
                            && isReadFrom(item.getAsJsonObject())) {
                        validatedEdges.add(item.getAsJsonObject());
                    }
                }
            }
        }
        Set<String> sourceRegions = strings(validatedEdges, "fromRegion");
        Set<String> terminalRegions = strings(validatedEdges, "toRegion");
        terminalRegions.removeAll(sourceRegions);
        if (terminalRegions.size() != 1) {
            throw new IOException(
                    "runtime read-from graph has no unique terminal target");
        }
        String terminalRegion = terminalRegions.iterator().next();
        List<Channel> result = new ArrayList<>();
        Set<String> dynamicEdges = new LinkedHashSet<>();
        for (RegionInstancePlan plan : plans) {
            for (Goal goal : plan.goals()) {
                if (!goal.kind().capturesOutputRelation()
                        || !"READY".equals(goal.admissionState())) {
                    continue;
                }
                OutputClosureContract closure = goal.outputClosure();
                if (closure == null) continue;
                for (OutputClosureContract.Member member
                        : closure.members()) {
                    String channelName = fieldName(member.cell());
                    for (JsonElement item : goal.edgeBindings()) {
                        if (!item.isJsonObject()) continue;
                        JsonObject edge = item.getAsJsonObject();
                        if (!isReadFrom(edge)
                                || !terminalRegion.equals(
                                string(edge, "toRegion"))
                                || !plan.regionId().equals(
                                string(edge, "fromRegion"))
                                || !plan.regionInstanceId().equals(
                                string(edge, "fromRegionInstance"))
                                || !member.cell().equals(
                                string(edge, "fromOutputCell"))) {
                            continue;
                        }
                        String edgeId = required(edge, "edgeId");
                        String dynamicEdge = edgeId + "\n"
                                + plan.regionInstanceId() + "\n"
                                + required(edge, "toRegionInstance") + "\n"
                                + member.portId() + "\n"
                                + required(edge, "toInputPort");
                        if (!dynamicEdges.add(dynamicEdge)) {
                            throw new IOException(
                                    "duplicate dynamic runtime edge: "
                                            + edgeId);
                        }
                        result.add(new Channel(channelName, member.cell(),
                                plan.regionId(), plan.regionInstanceId(),
                                goal.goalId(), edgeId,
                                terminalRegion,
                                required(edge, "toRegionInstance")));
                    }
                }
            }
        }
        result.sort(Comparator.comparing(Channel::sortKey));
        if (result.isEmpty()) {
            throw new IOException("runtime read-from discovery found no "
                    + "READY channels; output goals=" + outputGoalAdmissions());
        }
        Map<String, Channel> names = new TreeMap<>();
        for (Channel channel : result) {
            String key = channel.name.toLowerCase(Locale.ROOT);
            Channel previous = names.putIfAbsent(key, channel);
            if (previous != null && !previous.sameProducer(channel)) {
                throw new IOException(
                        "channel maps to conflicting producer demands: "
                                + channel.name);
            }
        }
        Set<String> targets = new LinkedHashSet<>();
        for (Channel channel : result) {
            targets.add(channel.targetRegionInstance);
        }
        if (targets.size() != 1) {
            throw new IOException(
                    "runtime channels do not converge on one target");
        }
        return result;
    }

    private List<String> outputGoalAdmissions() {
        List<String> result = new ArrayList<>();
        for (RegionInstancePlan plan : plans) {
            for (Goal goal : plan.goals()) {
                if (!goal.kind().capturesOutputRelation()) continue;
                result.add(plan.regionInstanceId() + "/" + goal.goalId()
                        + "=" + goal.admissionState() + ":"
                        + goal.admissionBlockers());
            }
        }
        return result;
    }

    /**
     * Discovers every output relation on a runtime-proven path to the target.
     * Terminal producer goals keep their field channel names; constructor and
     * other upstream state transformers receive deterministic internal
     * handles.  The shell can therefore execute one generic demand campaign
     * per goal while the composer receives the complete dependency chain.
     */
    private List<Demand> discoverDemands() throws IOException {
        String targetInstance = unique(channels, false);
        List<Demand> candidates = new ArrayList<>();
        for (RegionInstancePlan plan : plans) {
            for (Goal goal : plan.goals()) {
                if (!goal.kind().capturesOutputRelation()
                        || !"READY".equals(goal.admissionState())
                        || goal.outputClosure() == null) {
                    continue;
                }
                List<JsonObject> edges = new ArrayList<>();
                for (JsonElement item : goal.edgeBindings()) {
                    if (item.isJsonObject()
                            && isReadFrom(item.getAsJsonObject())) {
                        edges.add(item.getAsJsonObject());
                    }
                }
                if (!edges.isEmpty()) {
                    candidates.add(new Demand(plan, goal, edges));
                }
            }
        }

        Map<String, Set<String>> channelsByInstance = new LinkedHashMap<>();
        boolean changed;
        do {
            changed = false;
            for (Demand demand : candidates) {
                Set<String> names = new TreeSet<>();
                for (JsonObject edge : demand.edges) {
                    String downstream = string(edge,
                            "toRegionInstance");
                    if (targetInstance.equals(downstream)) {
                        names.add(fieldName(required(edge,
                                "fromOutputCell")));
                    } else {
                        names.addAll(channelsByInstance.getOrDefault(
                                downstream, java.util.Collections
                                        .<String>emptySet()));
                    }
                }
                if (demand.channels.addAll(names)) changed = true;
                Set<String> instanceChannels =
                        channelsByInstance.computeIfAbsent(
                                demand.regionInstanceId,
                                unused -> new TreeSet<>());
                if (instanceChannels.addAll(names)) changed = true;
            }
        } while (changed);

        List<Demand> result = new ArrayList<>();
        for (Demand candidate : candidates) {
            if (!candidate.channels.isEmpty()) result.add(candidate);
        }
        result.sort(Comparator.comparing(Demand::sortKey));
        if (result.isEmpty()) {
            throw new IOException("runtime read-from graph has no executable "
                    + "output demand path to target");
        }

        Set<String> terminalNames = new TreeSet<>(
                String.CASE_INSENSITIVE_ORDER);
        int upstream = 0;
        for (Demand demand : result) {
            if (demand.directlyFeeds(targetInstance)) {
                demand.handle = demand.channels.iterator().next();
                if (!terminalNames.add(demand.handle)) {
                    throw new IOException("channel belongs to multiple "
                            + "terminal producer demands: " + demand.handle);
                }
            }
        }
        for (Demand demand : result) {
            if (demand.handle.isEmpty()) {
                demand.handle = "UPSTREAM_" + (++upstream) + "_"
                        + String.join("_", demand.channels);
            }
        }
        result.sort(Comparator.comparing(demand -> demand.handle));
        return result;
    }

    private Target discoverTarget() throws IOException {
        String targetRegion = unique(channels, true);
        String targetInstance = unique(channels, false);
        List<Goal> goals = new ArrayList<>();
        for (RegionInstancePlan plan : plans) {
            if (!targetRegion.equals(plan.regionId())
                    || !targetInstance.equals(plan.regionInstanceId())) {
                continue;
            }
            for (Goal goal : plan.goals()) {
                if (goal.kind() == ClosureGoalKind.TARGET_REACH_CLOSURE
                        && ("READY".equals(goal.admissionState())
                        || "DISCOVERED".equals(goal.admissionState()))) {
                    goals.add(goal);
                }
            }
        }
        if (goals.size() != 1) {
            throw new IOException("expected one target reach closure for "
                    + targetInstance);
        }
        return new Target(targetRegion, targetInstance,
                goals.get(0).goalId());
    }

    private String scheduledProducerTask(String requested, Path taskPlan)
            throws IOException {
        Demand demand = demand(requested);
        List<String> matches = new ArrayList<>();
        for (JsonObject row : ArtifactIO.readJsonl(taskPlan)) {
            ExecutionTask task = ExecutionTask.decode(row);
            if (!demand.regionId.equals(task.regionId())
                    || !demand.regionInstanceId.equals(
                    task.regionInstanceId())
                    || !demand.goalId.equals(task.goalId())
                    || !task.goalKind().capturesOutputRelation()
                    || task.outputClosure() == null) {
                continue;
            }
            matches.add(task.taskId());
        }
        return only(matches, "scheduled producer task");
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
        return only(matches, "scheduled target task");
    }

    private Demand demand(String requested) throws IOException {
        List<Demand> matches = new ArrayList<>();
        for (Demand demand : demands) {
            if (demand.handle.equalsIgnoreCase(requested)) {
                matches.add(demand);
            }
        }
        if (matches.size() != 1) {
            throw new IOException(
                    "handle does not resolve to one producer demand: "
                            + requested);
        }
        return matches.get(0);
    }

    private void printDiscovery() {
        System.out.println("kind\tchannel\tregion\tinstance\tgoal");
        for (Demand demand : demands) {
            System.out.println("producer\t" + demand.handle + "\t"
                    + demand.regionId + "\t" + demand.regionInstanceId
                    + "\t" + demand.goalId);
        }
        System.out.println("target\t-\t" + target.regionId + "\t"
                + target.regionInstanceId + "\t" + target.goalId);
    }

    private static boolean isReadFrom(JsonObject edge) {
        return AutomaticRegionEdge.trustedRuntimeReadFromBinding(edge);
    }

    private static String fieldName(String cell) throws IOException {
        Matcher matcher = FIELD_CELL.matcher(cell);
        if (!matcher.matches()) {
            throw new IOException(
                    "output cell is not a declared field: " + cell);
        }
        return matcher.group(1).toUpperCase(Locale.ROOT);
    }

    private static Set<String> strings(Collection<JsonObject> rows,
                                       String field) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonObject row : rows) {
            String value = string(row, field);
            if (!value.isEmpty()) result.add(value);
        }
        return result;
    }

    private static String unique(List<Channel> channels, boolean region)
            throws IOException {
        Set<String> values = new LinkedHashSet<>();
        for (Channel channel : channels) {
            values.add(region
                    ? channel.targetRegion : channel.targetRegionInstance);
        }
        if (values.size() != 1) {
            throw new IOException("ambiguous target "
                    + (region ? "region" : "instance"));
        }
        return values.iterator().next();
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
            throw new IOException("missing " + field);
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

    private static final class Channel {
        private final String name;
        private final String fromCell;
        private final String regionId;
        private final String regionInstanceId;
        private final String goalId;
        private final String edgeId;
        private final String targetRegion;
        private final String targetRegionInstance;

        private Channel(String name, String fromCell,
                        String regionId, String regionInstanceId,
                        String goalId, String edgeId,
                        String targetRegion, String targetRegionInstance) {
            this.name = name;
            this.fromCell = fromCell;
            this.regionId = regionId;
            this.regionInstanceId = regionInstanceId;
            this.goalId = goalId;
            this.edgeId = edgeId;
            this.targetRegion = targetRegion;
            this.targetRegionInstance = targetRegionInstance;
        }

        private boolean sameProducer(Channel other) {
            return fromCell.equals(other.fromCell)
                    && regionId.equals(other.regionId)
                    && regionInstanceId.equals(other.regionInstanceId)
                    && goalId.equals(other.goalId);
        }

        private String sortKey() {
            return regionInstanceId + "\n" + goalId + "\n" + name + "\n"
                    + edgeId;
        }
    }

    private static final class Demand {
        private String handle = "";
        private final Set<String> channels = new TreeSet<>();
        private final String regionId;
        private final String regionInstanceId;
        private final String goalId;
        private final List<JsonObject> edges;

        private Demand(RegionInstancePlan plan, Goal goal,
                       List<JsonObject> edges) {
            regionId = plan.regionId();
            regionInstanceId = plan.regionInstanceId();
            goalId = goal.goalId();
            this.edges = edges;
        }

        private boolean directlyFeeds(String instance) {
            for (JsonObject edge : edges) {
                if (instance.equals(string(edge, "toRegionInstance"))) {
                    return true;
                }
            }
            return false;
        }

        private String sortKey() {
            return regionInstanceId + "\n" + goalId;
        }
    }

    private static final class Target {
        private final String regionId;
        private final String regionInstanceId;
        private final String goalId;

        private Target(String regionId, String regionInstanceId,
                       String goalId) {
            this.regionId = regionId;
            this.regionInstanceId = regionInstanceId;
            this.goalId = goalId;
        }
    }
}
