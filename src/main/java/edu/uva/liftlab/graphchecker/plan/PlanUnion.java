package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.option.LongOptions;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.CanonicalJson;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * One seed replay for several targets of a batch campaign (ADHOC-INFRA WP3):
 * their task plans, each scheduled on its own slice over the batch's one
 * recording, grouped so that each group's union is a plan one replay runs.
 *
 * <p>The targets' plans stand on one recording and one weave, so they name
 * the same occurrences, and the tasks they share are one task (one id: the
 * occurrence, its region's content, its ports and, for a target's own
 * reach, its target branch).  A target joins the first group whose union it
 * agrees with: every occurrence both plan is the same task there, and every
 * tracked site both observe is the same observation (the weave refuses two).
 * Otherwise it opens a group of its own.  Two targets' different tasks at
 * one occurrence -- another body, or both reaching their own target there --
 * would need one task carrying several target branches, which the runtime
 * does not have: such targets replay apart.</p>
 *
 * <p>A group's union is its targets' tasks, each once, in order, every task
 * observing every site any of them observes (whichever occurrence reaches a
 * cell first starts its log), stamped with the union's own replay group
 * ({@link ConcolicScheduler#withSeedReplayGroup}).</p>
 *
 * <pre>
 *   --plan &lt;target&gt;=&lt;execution_task_plan.jsonl&gt;   (one per target, in order)
 *   --output-dir &lt;dir&gt;   groups.json [{group, targets}],
 *                        group-&lt;n&gt;/execution_task_plan.jsonl
 * </pre>
 */
public final class PlanUnion {
    static final String GROUPS = "groups.json";

    private PlanUnion() {
    }

    public static void main(String[] argv) throws IOException {
        LongOptions options = LongOptions.parse(argv);
        Path out = options.path("output-dir");
        if (out == null) {
            throw new IllegalArgumentException("--output-dir is required");
        }
        Map<String, List<JsonObject>> plans =
                new LinkedHashMap<String, List<JsonObject>>();
        for (String plan : options.all("plan")) {
            int equals = plan.indexOf('=');
            if (equals <= 0) {
                throw new IllegalArgumentException(
                        "--plan is <target>=<execution_task_plan.jsonl>: "
                                + plan);
            }
            plans.put(plan.substring(0, equals),
                    ArtifactIO.readJsonl(Paths.get(plan.substring(equals + 1))));
        }
        if (plans.isEmpty()) {
            throw new IllegalArgumentException("--plan is required");
        }
        List<Group> groups = groups(plans);
        Files.createDirectories(out);
        JsonArray summary = new JsonArray();
        for (int index = 0; index < groups.size(); index++) {
            Group group = groups.get(index);
            Path dir = out.resolve("group-" + index);
            Files.createDirectories(dir);
            ArtifactIO.replaceJsonl(dir.resolve("execution_task_plan.jsonl"),
                    group.rows());
            JsonObject row = new JsonObject();
            row.addProperty("group", index);
            JsonArray targets = new JsonArray();
            for (String target : group.targets) targets.add(target);
            row.add("targets", targets);
            row.addProperty("tasks", group.tasks.size());
            summary.add(row);
        }
        ArtifactIO.replace(out.resolve(GROUPS),
                CanonicalJson.render(summary) + "\n");
        System.out.println(CanonicalJson.render(summary));
    }

    /** The targets' groups: each joins the first it agrees with. */
    static List<Group> groups(Map<String, List<JsonObject>> plans) {
        List<Group> groups = new ArrayList<Group>();
        for (Map.Entry<String, List<JsonObject>> plan : plans.entrySet()) {
            Group joined = null;
            for (Group group : groups) {
                if (group.agrees(plan.getValue())) {
                    joined = group;
                    break;
                }
            }
            if (joined == null) {
                joined = new Group();
                groups.add(joined);
            }
            joined.add(plan.getKey(), plan.getValue());
        }
        return groups;
    }

    /** One seed replay's targets and its union. */
    static final class Group {
        final List<String> targets = new ArrayList<String>();
        /** Task id -> the task, in order. */
        final Map<String, JsonObject> tasks =
                new LinkedHashMap<String, JsonObject>();
        /** Occurrence -> the one task id there. */
        private final Map<String, String> byOccurrence =
                new LinkedHashMap<String, String>();
        /** Site -> its one observation, rendered. */
        private final Map<String, JsonObject> observed =
                new LinkedHashMap<String, JsonObject>();

        /** Whether one replay can run this plan beside the union. */
        boolean agrees(List<JsonObject> plan) {
            for (JsonObject task : plan) {
                String held = byOccurrence.get(occurrence(task));
                if (held != null && !held.equals(taskId(task))) return false;
                for (JsonElement site : array(task,
                        ExecutionTask.OBSERVED_SITES)) {
                    JsonObject observation = site.getAsJsonObject();
                    JsonObject other = observed.get(siteId(observation));
                    if (other != null && !CanonicalJson.render(other).equals(
                            CanonicalJson.render(observation))) {
                        return false;
                    }
                }
            }
            return true;
        }

        void add(String target, List<JsonObject> plan) {
            targets.add(target);
            for (JsonObject task : plan) {
                byOccurrence.putIfAbsent(occurrence(task), taskId(task));
                tasks.putIfAbsent(taskId(task), task);
                for (JsonElement site : array(task,
                        ExecutionTask.OBSERVED_SITES)) {
                    observed.putIfAbsent(siteId(site.getAsJsonObject()),
                            site.getAsJsonObject());
                }
            }
        }

        /** The union: every task once, every task observing every site. */
        List<JsonObject> rows() {
            JsonArray sites = new JsonArray();
            for (JsonObject site : observed.values()) sites.add(site);
            List<JsonObject> rows = new ArrayList<JsonObject>();
            for (JsonObject task : tasks.values()) {
                JsonObject row = task.deepCopy();
                row.remove(ConcolicScheduler.REPLAY_GROUP_ID);
                row.remove(ExecutionTask.OBSERVED_SITES);
                if (sites.size() > 0) {
                    row.add(ExecutionTask.OBSERVED_SITES, sites.deepCopy());
                }
                rows.add(row);
            }
            return ConcolicScheduler.withSeedReplayGroup(rows);
        }
    }

    private static String taskId(JsonObject task) {
        return optionalString(task, "taskId");
    }

    private static String occurrence(JsonObject task) {
        return optionalString(task, "occurrenceId");
    }

    private static String siteId(JsonObject observation) {
        return optionalString(observation, SiteId.MEMBER);
    }
}
