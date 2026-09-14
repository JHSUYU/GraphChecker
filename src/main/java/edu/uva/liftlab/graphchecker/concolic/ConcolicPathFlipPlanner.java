package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * Plans the deterministic branch-flip frontier for every region of one
 * closure wave. Solving and executing an exact task belong to
 * {@link ConcolicPathFlipSolver}; keeping those operations separate lets one
 * immutable frontier feed many independent worker processes.
 *
 * <p>A wave's members all read the same summaries and the same task plan, so
 * resolving each replay's own path conditions is one indexing pass, not one per
 * member. This process performs it once and then plans each member from it;
 * each member still writes its own {@code region_path_manifest.json} and
 * {@code region_path_worklist.jsonl} in its own directory, exactly as when
 * each member had its own JVM.</p>
 */
public final class ConcolicPathFlipPlanner {
    private static final Gson PRETTY = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();

    private ConcolicPathFlipPlanner() {
    }

    public static void main(String[] argv) throws Exception {
        Map<String, String> options = options(argv);
        List<Member> members = members(requiredPath(options, "members"));
        Wave wave = Wave.load(options);
        boolean executable = true;
        for (Member member : members) {
            JsonObject manifest = wave.plan(member);
            System.out.println(PRETTY.toJson(manifest));
            String state = optionalString(manifest, "state");
            if (RegionPathWorklist.State.GAPPED.name().equals(state)
                    || RegionPathWorklist.State.NOT_STARTED.name().equals(
                            state)) {
                executable = false;
            }
        }
        if (!executable) {
            System.exit(2);
        }
    }

    /** One region/goal of the wave and the directory it publishes into. */
    private static final class Member {
        private final String regionId;
        private final String goalId;
        private final Path directory;

        private Member(String regionId, String goalId, Path directory) {
            this.regionId = regionId;
            this.goalId = goalId;
            this.directory = directory;
        }
    }

    /**
     * Reads the wave roster: one {@code regionId\tgoalId\toutputDir} line per
     * member, in the schedule index's order.
     */
    private static List<Member> members(Path roster) throws IOException {
        List<Member> members = new ArrayList<>();
        for (String line : Files.readAllLines(roster,
                StandardCharsets.UTF_8)) {
            if (line.trim().isEmpty()) continue;
            String[] cells = line.split("\t", -1);
            if (cells.length != 3 || cells[1].trim().isEmpty()
                    || cells[2].trim().isEmpty()) {
                throw new IllegalArgumentException("wave member roster needs "
                        + "regionId<TAB>goalId<TAB>outputDir, got: " + line);
            }
            members.add(new Member(cells[0], cells[1],
                    Paths.get(cells[2])));
        }
        if (members.isEmpty()) {
            throw new IllegalArgumentException(
                    "wave member roster names no member: " + roster);
        }
        return members;
    }

    /**
     * Everything a wave's members share: the frozen task plan, the propagated
     * summaries and the one family snapshot they are all planned against.
     */
    static final class Wave {
        private final List<JsonObject> allExecutionTasks;
        private final List<JsonObject> allSummaries;
        /** Every communication port some replay of this wave attached. */
        private final java.util.Set<String> deliveredHandoffPorts;
        private final List<JsonObject> allRecords;
        /** The wave's receiver-family rows, indexed by their family key.
         *  Expanded, so the transitive family walk below sees every nested
         *  family name instead of a Merkle reference to one. */
        /** The families each dependency row names, walked once per wave
         *  rather than once per flip row that reaches it. */
        private final Map<String, Set<String>> nestedFamilies =
                new LinkedHashMap<>();
        private final String topologyEpoch;
        private final RegionPathWorklist.Bounds bounds;
        /** The wave's declared roots, computed once for every member.
         *  Built from the whole wave: a root minted in one region is still a
         *  root when another region's branch consumes it. */
        private final SymbolicRootInventory roots;
        /** One in-session resolver per replay of this wave's corpus. */
        private final java.util.Map<String, InSessionReadResolver> resolvers;
        /**
         * The wave's handoff families: what each wire delivery of this
         * corpus may be.  An obligation answers a handoff, and the replay
         * applies that answer at the attach, so an unconstrained v_H let
         * the solver hypothesise values no producer makes.  The arms are
         * the corpus's own, selected here where every replay's rows are.
         */
        private final HandoffFamilyRows.Corpus families;
        /** One verification of the wave's table, shared by every member. */
        private final SharedExpressionTable.Compactor compactor =
                new SharedExpressionTable.Compactor();

        private Wave(List<JsonObject> allExecutionTasks,
                     List<JsonObject> allSummaries,
                     List<JsonObject> allRecords,
                     String topologyEpoch,
                     RegionPathWorklist.Bounds bounds,
                     SymbolicRootInventory roots,
                     HandoffFamilyRows.Corpus families) {
            this.families = families;
            this.allExecutionTasks = allExecutionTasks;
            this.allSummaries = allSummaries;
            this.deliveredHandoffPorts =
                    RegionPathWorklist.attachedHandoffPorts(allSummaries);
            this.allRecords = allRecords;
            this.topologyEpoch = topologyEpoch;
            this.bounds = bounds;
            this.roots = roots;
            this.resolvers = ResolvedFlipQuery.resolversByReplay(
                    allSummaries);
        }

        private static Wave load(Map<String, String> options)
                throws IOException {
            List<JsonObject> allExecutionTasks = ArtifactIO.readJsonl(
                    requiredPath(options, "task-plan"));
            // Rows arrive content-addressed; the wave plans over one
            // expanded DAG, as the closure used to expand them on its way
            // through.
            List<JsonObject> observedSummaries =
                    SharedExpressionTable.expandAll(ArtifactIO.readJsonl(
                            requiredPath(options, "summaries")));
            // The summaries are read as the replays published them.  The
            // closure used to rewrite them first, replacing each shared read
            // with a choice over the writers the region graph could find --
            // and an obligation cut from that asks the solver to pick a
            // writer, which is the opposite of asking it for a root.  Each
            // path condition is resolved inside its own replay instead, by
            // ResolvedFlipQuery, where the value is a fact rather than a
            RegionPathWorklist.Bounds defaults =
                    RegionPathWorklist.Bounds.defaults();
            // The roots are the wave's, not a member's: read them from the
            // summaries the members will actually plan against and from the
            // plan that declares them.
            SymbolicRootInventory roots = SymbolicRootInventory.of(
                    observedSummaries, allExecutionTasks);
            // What the case declares its roots may be.  A family arm is
            // only as constraining as the roots inside it -- "v_H is the
            // serial number" says nothing while the serial number is free
            // -- and the case file is the one authority on that, exactly
            // as it is for the composition.  Absent, every root is pinned
            // to what the recording read, which is the composition's
            // default too.
            String domains = optional(options, "root-domains");
            return new Wave(allExecutionTasks, observedSummaries,
                    rows(options, "records"),
                    optional(options, "topology-epoch"),
                    new RegionPathWorklist.Bounds(
                            count(options, "max-paths-per-region",
                                    defaults.maxPathsPerRegion),
                            count(options, "max-flips-per-path",
                                    defaults.maxFlipsPerPath),
                            count(options, "max-tasks", defaults.maxTasks)),
                    roots,
                    HandoffFamilyRows.Corpus.of(observedSummaries,
                            domains.isEmpty() ? null : Paths.get(domains)));
        }

        /** Publishes one member's worklist and manifest; returns the manifest. */
        private JsonObject plan(Member member) throws IOException {
            String regionId = member.regionId;
            String goalId = member.goalId;
            List<JsonObject> executionTasks = new ArrayList<>();
            for (JsonObject task : allExecutionTasks) {
                if ((regionId.isEmpty()
                        || regionId.equals(optionalString(task, "regionId")))
                        && goalId.equals(optionalString(task, "goalId"))) {
                    executionTasks.add(task);
                }
            }
            Map<String, JsonObject> taskById = ArtifactIO.uniqueIndex(
                    executionTasks, "taskId");
            List<JsonObject> summaries = new ArrayList<>();
            for (JsonObject summary : allSummaries) {
                if (taskById.containsKey(optionalString(summary, "taskId"))
                        && (regionId.isEmpty()
                        || regionId.equals(optionalString(summary,
                                "regionId")))
                        && goalId.equals(optionalString(summary, "goalId"))) {
                    summaries.add(summary);
                }
            }
            List<JsonObject> explorationRecords = new ArrayList<>();
            for (JsonObject record : allRecords) {
                if ((regionId.isEmpty()
                        || regionId.equals(optionalString(record, "regionId")))
                        && goalId.equals(optionalString(record, "goalId"))) {
                    explorationRecords.add(record);
                }
            }
            // The wave's deliveries, not this member's.  A member's
            // summaries are its own region's, so a handoff gap it imports
            // for a port another region consumes could never be shown
            // delivered from them -- the same "across the group, not this
            // path's own summary" lesson controlBySymbol below already
            // carries, for the same rows.
            RegionPathWorklist.Result result = RegionPathWorklist.plan(
                    summaries, executionTasks, explorationRecords, bounds,
                    roots, deliveredHandoffPorts);
            for (JsonObject task : result.tasks) {
                // The obligation asks for a root valuation, so its path
                // condition has to be an expression over roots.  Resolve it
                // here, where the replay it was cut from still has its rows.
                String replay = replayOfSource(task);
                ResolvedFlipQuery.attach(task, resolvers.get(replay), replay);
                // The controls this obligation flips through.  A HOFF label
                // IS the identity of the attach that minted it, and that
                // attach happened in this same replay run -- in whichever
                // region activation's summary of this replay group made it.
                // Looking only at the flipped path's own summary found one
                // attach where the model assigned five, and every such model
                // was refused as not materializable.  Symbol to row, across
                // the group; no boundary, no write log, no inference.
                controlBySymbol(task, replay, allSummaries,
                        result.manifest);
                // And what each of those handoffs may be answered with.
                // The obligation's model is applied at the attach by the
                // next replay, so a control with no family is a control the
                // solver may answer with a value the system never produces:
                // 17897's five block-key handoffs were answered 1,1,1,1,0
                // beside recordings of 119992..119995, the replay threw,
                // and every composition then refused the path.  The arms
                // are the same rows the composition merges.
                HandoffFamilyRows.attach(task, families);
                task.addProperty(VmExpressionIr.TOPOLOGY_EPOCH,
                        topologyEpoch);
            }
            if (!topologyEpoch.isEmpty()) {
                result.manifest.addProperty(VmExpressionIr.TOPOLOGY_EPOCH,
                        topologyEpoch);
            }
            result.manifest.add("symbolicPropagationGaps", new JsonArray());
            // A worklist repeats the same upstream PCs in several independent
            // flip rows.  Preserve the portable one-row contract while storing
            // their immutable expression DAG once per row as Merkle references.
            // Solver workers expand only the one query they select.  The rows
            // of a wave draw on one common pool of definitions, so one
            // compactor verifies each definition once for the whole wave
            // instead of once per row; each row still publishes only the
            // definitions reachable from its own constraints and its own
            // scoped family evidence.
            for (int index = 0; index < result.tasks.size(); index++) {
                result.tasks.set(index, compactor.compact(
                        result.tasks.get(index)));
            }
            Collections.sort(result.tasks, Comparator.comparing(
                    task -> optionalString(task, "queryKey")));

            ArtifactIO.replaceJsonl(member.directory.resolve(
                    "region_path_worklist.jsonl"), result.tasks);
            ArtifactIO.replace(member.directory.resolve(
                    "region_path_manifest.json"),
                    PRETTY.toJson(result.manifest) + System.lineSeparator());
            return result.manifest;
        }

        /** The replay this obligation was cut from. */
        /**
         * Answers every handoff variable this obligation mentions.
         *
         * <p>One row per {@code HOFF.} label the resolved flip query names,
         * found by that label among the {@code VM_HANDOFF_EVENT} rows of
         * every summary of this replay group -- the attach that minted it.
         * A label no summary of the group minted is named instead, because
         * an obligation that cannot answer a variable its own flip assigns
         * is one the replay cannot run.</p>
         */
        static void controlBySymbol(JsonObject task, String replay,
                                    List<JsonObject> allSummaries,
                                    JsonObject manifest) {
            Set<String> wanted = new LinkedHashSet<>();
            handoffLabels(ResolvedFlipQuery.of(task), wanted,
                    new java.util.IdentityHashMap<JsonElement, Boolean>());
            if (wanted.isEmpty()) return;
            Map<String, JsonObject> rows = new LinkedHashMap<>();
            for (JsonObject summary : allSummaries) {
                if (!replay.equals(ResolvedFlipQuery.replayKey(summary))) {
                    continue;
                }
                for (JsonElement encoded
                        : JsonFields.array(summary, VmHandoffEvidence.FIELD)) {
                    if (!encoded.isJsonObject()) continue;
                    JsonObject event = encoded.getAsJsonObject();
                    String symbol = optionalString(event,
                            InSessionReadResolver.HANDOFF_SYMBOL);
                    String phase = optionalString(event,
                            InSessionReadResolver.HANDOFF_PHASE_ID);
                    if (!wanted.contains(symbol) || phase.isEmpty()) continue;
                    JsonObject control = new JsonObject();
                    control.addProperty("rawSymbol", symbol);
                    control.addProperty(
                            InSessionReadResolver.HANDOFF_PHASE_ID, phase);
                    control.addProperty("javaType",
                            optionalString(event, "javaType"));
                    control.addProperty("recordedValue",
                            optionalString(event, "recordedValue"));
                    control.addProperty("consumerOccurrenceId",
                            optionalString(summary, "occurrenceId"));
                    rows.putIfAbsent(symbol, control);
                }
            }
            JsonArray controls = new JsonArray();
            for (JsonObject row : rows.values()) controls.add(row);
            if (controls.size() > 0) {
                task.add(RegionPathWorklist.HANDOFF_CONTROLS, controls);
            }
            for (String symbol : wanted) {
                if (rows.containsKey(symbol)) continue;
                JsonObject gap = new JsonObject();
                gap.addProperty("kind", "HANDOFF_CONTROL_ROW_ABSENT");
                gap.addProperty("reason",
                        "NO_SUMMARY_OF_THE_REPLAY_MINTED_THIS_HANDOFF");
                gap.addProperty("subject", symbol);
                gap.addProperty("queryKey", optionalString(task, "queryKey"));
                JsonFields.array(manifest, "gaps").add(gap);
            }
        }

        /** Every {@code HOFF.} label one resolved query names. */
        private static void handoffLabels(
                JsonElement value, Set<String> into,
                Map<JsonElement, Boolean> visited) {
            if (value == null || value.isJsonNull()) return;
            if (value.isJsonPrimitive()) {
                String text = value.getAsJsonPrimitive().isString()
                        ? value.getAsString() : "";
                if (text.startsWith("M_") && text.contains(
                        edu.uva.liftlab.graphchecker.contract.HandoffPhaseContract.LABEL_PREFIX)) {
                    into.add(text);
                }
                return;
            }
            if (visited.put(value, Boolean.TRUE) != null) return;
            if (value.isJsonArray()) {
                for (JsonElement child : value.getAsJsonArray()) {
                    handoffLabels(child, into, visited);
                }
                return;
            }
            for (Map.Entry<String, JsonElement> field
                    : value.getAsJsonObject().entrySet()) {
                handoffLabels(field.getValue(), into, visited);
            }
        }

        private String replayOfSource(JsonObject task) {
            String summaryId = optionalString(task, "sourceSummaryId");
            String taskId = optionalString(task, "sourceTaskId");
            for (JsonObject summary : allSummaries) {
                if (!summaryId.isEmpty() && summaryId.equals(
                        optionalString(summary, "summaryId"))) {
                    return ResolvedFlipQuery.replayKey(summary);
                }
            }
            for (JsonObject summary : allSummaries) {
                if (!taskId.isEmpty() && taskId.equals(
                        optionalString(summary, "taskId"))) {
                    return ResolvedFlipQuery.replayKey(summary);
                }
            }
            return "";
        }

    }



    private static List<JsonObject> rows(Map<String, String> options,
                                         String name) throws IOException {
        String path = options.get(name);
        return path == null || path.trim().isEmpty()
                ? Collections.<JsonObject>emptyList()
                : ArtifactIO.readJsonl(Paths.get(path));
    }

    private static int count(Map<String, String> options, String name,
                             int fallback) {
        return Math.toIntExact(number(options, name, fallback));
    }

    /** The {@code --name value} pairs of one worker invocation; shared with
     *  {@link ConcolicPathFlipSolver}, which is launched the same way. */
    static Map<String, String> options(String[] argv) {
        return CliArgs.pairs(argv);
    }

    static String optional(Map<String, String> options, String name) {
        String value = options.get(name);
        return value == null ? "" : value;
    }

    static String requiredValue(Map<String, String> options, String name) {
        String value = optional(options, name);
        if (value.trim().isEmpty()) {
            throw new IllegalArgumentException("Missing --" + name);
        }
        return value;
    }

    static Path requiredPath(Map<String, String> options, String name) {
        return Paths.get(requiredValue(options, name));
    }

    static long number(Map<String, String> options, String name,
                       long fallback) {
        String value = options.get(name);
        return value == null || value.trim().isEmpty()
                ? fallback : Long.parseLong(value);
    }
}
