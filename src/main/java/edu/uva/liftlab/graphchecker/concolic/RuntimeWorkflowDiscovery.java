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

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
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
        demands = groupDemands(channels);
        target = discoverTarget();
    }

    public static void main(String[] argv) throws Exception {
        Map<String, String> args = parseArgs(argv);
        String command = required(args, "command");
        RuntimeWorkflowDiscovery discovery = new RuntimeWorkflowDiscovery(
                Paths.get(required(args, "region-plan")));
        switch (command) {
            case "validate":
                return;
            case "discover":
                discovery.printDiscovery();
                return;
            case "producer-channels":
                for (Demand demand : discovery.demands) {
                    System.out.println(demand.ownerChannel);
                }
                return;
            case "resolve-channel":
                System.out.println(discovery.channel(
                        required(args, "channel")).name);
                return;
            case "owner-channel":
                System.out.println(discovery.demand(
                        required(args, "channel")).ownerChannel);
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
        Set<String> edgeIds = new LinkedHashSet<>();
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
                        if (!edgeIds.add(edgeId)) {
                            throw new IOException(
                                    "duplicate runtime edgeId: " + edgeId);
                        }
                        result.add(new Channel(channelName, member.cell(),
                                required(edge, "toInputCell"),
                                plan.regionId(), plan.regionInstanceId(),
                                goal.goalId(), closure.demandKey(),
                                closure.closureFingerprint(), edgeId,
                                terminalRegion,
                                required(edge, "toRegionInstance")));
                    }
                }
            }
        }
        result.sort(Comparator.comparing(Channel::sortKey));
        if (result.isEmpty()) {
            throw new IOException(
                    "runtime read-from discovery found no channels");
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

    private static List<Demand> groupDemands(List<Channel> channels)
            throws IOException {
        Map<String, List<Channel>> grouped = new TreeMap<>();
        for (Channel channel : channels) {
            String key = channel.regionInstanceId + "\n" + channel.goalId
                    + "\n" + channel.demandKey + "\n"
                    + channel.closureFingerprint;
            grouped.computeIfAbsent(key, unused -> new ArrayList<>())
                    .add(channel);
        }
        List<Demand> result = new ArrayList<>();
        Set<String> claimedChannels = new TreeSet<>(
                String.CASE_INSENSITIVE_ORDER);
        for (List<Channel> group : grouped.values()) {
            TreeSet<String> names = new TreeSet<>();
            for (Channel channel : group) {
                names.add(channel.name);
                if (!claimedChannels.add(channel.name)) {
                    throw new IOException(
                            "channel belongs to multiple producer demands: "
                                    + channel.name);
                }
            }
            result.add(new Demand(group.get(0), names.iterator().next(),
                    names));
        }
        result.sort(Comparator.comparing(demand -> demand.ownerChannel));
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
        Channel channel = channel(requested);
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
            for (OutputClosureContract.Member member
                    : task.outputClosure().members()) {
                if (channel.fromCell.equals(member.cell())) {
                    matches.add(task.taskId());
                    break;
                }
            }
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

    private Channel channel(String requested) throws IOException {
        List<Channel> matches = new ArrayList<>();
        for (Channel channel : channels) {
            if (channel.name.equalsIgnoreCase(requested)
                    && matches.stream().noneMatch(existing ->
                    existing.name.equals(channel.name))) {
                matches.add(channel);
            }
        }
        if (matches.size() != 1) {
            throw new IOException(
                    "channel is not discovered exactly once: " + requested);
        }
        return matches.get(0);
    }

    private Demand demand(String requested) throws IOException {
        String canonical = channel(requested).name;
        List<Demand> matches = new ArrayList<>();
        for (Demand demand : demands) {
            if (demand.channels.contains(canonical)) matches.add(demand);
        }
        if (matches.size() != 1) {
            throw new IOException(
                    "channel does not resolve to one producer demand: "
                            + requested);
        }
        return matches.get(0);
    }

    private void printDiscovery() {
        System.out.println("kind\tchannel\tregion\tinstance\tgoal");
        for (Demand demand : demands) {
            for (String channel : demand.channels) {
                System.out.println("producer\t" + channel + "\t"
                        + demand.regionId + "\t" + demand.regionInstanceId
                        + "\t" + demand.goalId);
            }
        }
        System.out.println("target\t-\t" + target.regionId + "\t"
                + target.regionInstanceId + "\t" + target.goalId);
    }

    private static boolean isReadFrom(JsonObject edge) {
        String kind = string(edge, "evidenceKind");
        JsonElement writer = edge.get("writerEventSeq");
        JsonElement reader = edge.get("readerEventSeq");
        JsonElement receiver = edge.get("receiverObjectId");
        return ("FIELD_ASSIGNMENT_READ_FROM_V1".equals(kind)
                || "CONTAINER_MUTATION_READ_FROM_V1".equals(kind))
                && writer != null && writer.isJsonPrimitive()
                && writer.getAsJsonPrimitive().isNumber()
                && reader != null && reader.isJsonPrimitive()
                && reader.getAsJsonPrimitive().isNumber()
                && receiver != null && receiver.isJsonPrimitive()
                && receiver.getAsJsonPrimitive().isNumber()
                && longInteger(edge, "writerEventSeq", 0L)
                < longInteger(edge, "readerEventSeq", 0L)
                && longInteger(edge, "receiverObjectId", 0L) != 0L;
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
        private final String toCell;
        private final String regionId;
        private final String regionInstanceId;
        private final String goalId;
        private final String demandKey;
        private final String closureFingerprint;
        private final String edgeId;
        private final String targetRegion;
        private final String targetRegionInstance;

        private Channel(String name, String fromCell, String toCell,
                        String regionId, String regionInstanceId,
                        String goalId, String demandKey,
                        String closureFingerprint, String edgeId,
                        String targetRegion, String targetRegionInstance) {
            this.name = name;
            this.fromCell = fromCell;
            this.toCell = toCell;
            this.regionId = regionId;
            this.regionInstanceId = regionInstanceId;
            this.goalId = goalId;
            this.demandKey = demandKey;
            this.closureFingerprint = closureFingerprint;
            this.edgeId = edgeId;
            this.targetRegion = targetRegion;
            this.targetRegionInstance = targetRegionInstance;
        }

        private boolean sameProducer(Channel other) {
            return fromCell.equals(other.fromCell)
                    && regionId.equals(other.regionId)
                    && regionInstanceId.equals(other.regionInstanceId)
                    && goalId.equals(other.goalId)
                    && demandKey.equals(other.demandKey)
                    && closureFingerprint.equals(other.closureFingerprint);
        }

        private String sortKey() {
            return regionInstanceId + "\n" + goalId + "\n" + demandKey
                    + "\n" + closureFingerprint + "\n" + name + "\n"
                    + edgeId;
        }
    }

    private static final class Demand {
        private final String ownerChannel;
        private final Set<String> channels;
        private final String regionId;
        private final String regionInstanceId;
        private final String goalId;

        private Demand(Channel channel, String ownerChannel,
                       Set<String> channels) {
            this.ownerChannel = ownerChannel;
            this.channels = channels;
            regionId = channel.regionId;
            regionInstanceId = channel.regionInstanceId;
            goalId = channel.goalId;
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
