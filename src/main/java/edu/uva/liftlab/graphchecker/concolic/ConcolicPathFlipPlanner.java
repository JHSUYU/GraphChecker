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
    private static final class Wave {
        private final List<JsonObject> allExecutionTasks;
        private final List<JsonObject> allSummaries;
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
        /** One verification of the wave's table, shared by every member. */
        private final SharedExpressionTable.Compactor compactor =
                new SharedExpressionTable.Compactor();

        private Wave(List<JsonObject> allExecutionTasks,
                     List<JsonObject> allSummaries,
                     List<JsonObject> allRecords,
                     String topologyEpoch,
                     RegionPathWorklist.Bounds bounds,
                     SymbolicRootInventory roots) {
            this.allExecutionTasks = allExecutionTasks;
            this.allSummaries = allSummaries;
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
            return new Wave(allExecutionTasks, observedSummaries,
                    rows(options, "records"),
                    optional(options, "topology-epoch"),
                    new RegionPathWorklist.Bounds(
                            count(options, "max-paths-per-region",
                                    defaults.maxPathsPerRegion),
                            count(options, "max-flips-per-path",
                                    defaults.maxFlipsPerPath),
                            count(options, "max-tasks", defaults.maxTasks)),
                    roots);
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
            RegionPathWorklist.Result result = RegionPathWorklist.plan(
                    summaries, executionTasks, explorationRecords, bounds,
                    roots);
            for (JsonObject task : result.tasks) {
                // The obligation asks for a root valuation, so its path
                // condition has to be an expression over roots.  Resolve it
                // here, where the replay it was cut from still has its rows.
                String replay = replayOfSource(task);
                ResolvedFlipQuery.attach(task, resolvers.get(replay), replay);
                JsonObject bundle = LinkedReplayBundle.create(
                        optionalString(task, "sourceTaskId"),
                        allExecutionTasks, allSummaries,
                        optionalString(task, "sourceSummaryId"),
                        topologyEpoch);
                task.add(LinkedReplayBundle.FIELD, bundle);
            }
            if (!topologyEpoch.isEmpty()) {
                result.manifest.addProperty(
                        LinkedReplayBundle.TOPOLOGY_EPOCH_FIELD,
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
