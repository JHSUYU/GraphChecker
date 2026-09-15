package edu.uva.liftlab.graphchecker.d3.explore;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.d3.contract.GapClass;
import edu.uva.liftlab.graphchecker.d3.contract.GapKind;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.Task;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * EXPLORE, one wave: plan the closure, propose the flips still open.
 *
 * <pre>
 *   --sessions &lt;dir&gt;           the corpus (the campaign's own layout), or
 *   --iteration &lt;dir&gt;          its parent, which holds sessions/
 *   --task-plan &lt;file&gt;         the seed replay's plan; its occurrences are
 *                              the closure's roots
 *   --target-occurrence &lt;addr&gt; one more root, in v2 or either v1 spelling
 *   --results &lt;file&gt;           every ObligationResult the waves before this
 *                              one recorded; a query answered there is never
 *                              proposed again
 *   --root-domains &lt;file&gt;      what the CASE says each root may be
 *   --wave &lt;n&gt;                 which wave this is
 *   --topology-epoch &lt;id&gt;      the epoch these sessions belong to
 *   --output-dir &lt;dir&gt;         obligations.jsonl, tasks.jsonl, gaps.jsonl,
 *                              root-domains.jsonl, explore_manifest.json
 *   --max-tasks / --max-paths-per-region / --max-flips-per-path
 * </pre>
 *
 * <p>ONE invocation is ONE wave: the campaign owns the loop, because it also
 * owns the workers that solve and replay what a wave proposes.  This process
 * reads every session the epoch has produced -- including the ones the last
 * wave's replays wrote -- rebuilds the frontier from the recorded verdicts,
 * and writes the flips no wave has answered yet.  It never solves: a query
 * costs a z3 run, and the campaign runs those one worker per obligation
 * ({@link ObligationSolverMain}).</p>
 */
public final class ExploreMain {
    private ExploreMain() {
    }

    public static void main(String[] argv) throws Exception {
        Map<String, String> options = options(argv);
        Path sessions = path(options, "sessions");
        Path iteration = path(options, "iteration");
        if (iteration == null && sessions != null) {
            iteration = sessions.getParent();
        }
        if (iteration == null) {
            throw new IllegalArgumentException(
                    "Missing --sessions (or --iteration)");
        }
        Path out = path(options, "output-dir");
        if (out == null) out = path(options, "out");
        if (out == null) {
            throw new IllegalArgumentException("Missing --output-dir");
        }
        JsonObject manifest = plan(iteration, anchors(options),
                path(options, "root-domains"), path(options, "results"), out,
                (int) number(options, "wave", 0),
                value(options, "topology-epoch", ""),
                (int) number(options, "max-tasks",
                        ClosurePlanner.DEFAULT_MAX_TASKS),
                new ObligationFactory.Bounds(
                        (int) number(options, "max-paths-per-region",
                                ObligationFactory.DEFAULT_MAX_PATHS_PER_TASK),
                        (int) number(options, "max-flips-per-path",
                                ObligationFactory.DEFAULT_MAX_FLIPS_PER_PATH)));
        System.out.println(pretty(manifest));
    }

    /**
     * Plans one wave.
     *
     * @param roots the occurrences the closure starts from: the declared
     *              anchor, or the seed plan's own occurrences
     */
    public static JsonObject plan(Path iteration,
                                  List<OccurrenceAddress> roots,
                                  Path rootDomains, Path results, Path out,
                                  int wave, String topologyEpoch,
                                  int maxTasks,
                                  ObligationFactory.Bounds bounds)
            throws IOException {
        Corpus corpus = Corpus.read(iteration, rootDomains);
        List<Task> tasks = new ArrayList<Task>();
        List<GapRow> gaps = new ArrayList<GapRow>();
        Set<String> planned = new LinkedHashSet<String>();
        for (OccurrenceAddress root : roots) {
            if (corpus.pathsOf(root).isEmpty()) {
                gaps.add(GapRow.of("", GapKind.ADMISSION_GAP,
                        GapClass.DIAGNOSTIC, root.render(),
                        "no session of this epoch activated the occurrence "
                                + "the plan names, so its closure is empty"));
            }
            ClosurePlanner.Plan plan = ClosurePlanner.plan(corpus, root,
                    maxTasks);
            gaps.addAll(plan.gaps);
            for (Task task : plan.tasks) {
                if (planned.add(task.taskId())) tasks.add(task);
            }
        }
        Frontier frontier = new Frontier(tasks);
        frontier.consume(RowCodec.readAll(results,
                ExploreCodec::readResult));
        List<ObligationFactory.Candidate> candidates =
                new ArrayList<ObligationFactory.Candidate>();
        for (Task task : tasks) {
            candidates.addAll(ObligationFactory.candidates(corpus, task,
                    bounds, frontier::asked));
        }
        Frontier.Wave open = frontier.open(wave, candidates);

        Files.createDirectories(out);
        RowCodec.writeAll(out.resolve("tasks.jsonl"), tasks,
                ExploreCodec::writeTask);
        // An empty file IS the frontier closing: the stage breaks its loop
        // on it, and a wave that has nothing to ask must not have to say so
        // in a row that nothing executes.
        RowCodec.writeAll(out.resolve("obligations.jsonl"), open.obligations,
                ExploreCodec::writeObligation);
        RowCodec.writeAll(out.resolve("gaps.jsonl"), distinct(gaps),
                RowCodec::writeGap);
        JsonObject manifest = manifest(roots, tasks, frontier, open,
                topologyEpoch, gaps);
        Files.write(out.resolve("explore_manifest.json"),
                (pretty(manifest) + System.lineSeparator())
                        .getBytes(StandardCharsets.UTF_8));
        return manifest;
    }

    /** The closure's roots: the declared anchor and the seed plan's own. */
    private static List<OccurrenceAddress> anchors(Map<String, String> options)
            throws IOException {
        List<OccurrenceAddress> roots = new ArrayList<OccurrenceAddress>();
        Set<String> seen = new LinkedHashSet<String>();
        String declared = value(options, "target-occurrence", "");
        if (!declared.isEmpty()) {
            OccurrenceAddress anchor = OccurrenceAddress.parse(declared);
            seen.add(anchor.id());
            roots.add(anchor);
        }
        Path plan = path(options, "task-plan");
        if (plan != null && Files.isRegularFile(plan)) {
            for (JsonObject row : RowCodec.readJsonl(plan)) {
                JsonElement occurrence = row.get("occurrenceId");
                if (occurrence == null || !occurrence.isJsonPrimitive()) {
                    continue;
                }
                OccurrenceAddress address;
                try {
                    address = OccurrenceAddress.parse(
                            occurrence.getAsString());
                } catch (IllegalArgumentException malformed) {
                    continue;
                }
                if (seen.add(address.id())) roots.add(address);
            }
        }
        if (roots.isEmpty()) {
            throw new IllegalArgumentException("the closure has no root: "
                    + "pass --target-occurrence, or a --task-plan whose rows "
                    + "name an occurrenceId");
        }
        return roots;
    }

    private static JsonObject manifest(List<OccurrenceAddress> roots,
                                       List<Task> tasks, Frontier frontier,
                                       Frontier.Wave open,
                                       String topologyEpoch,
                                       List<GapRow> gaps) {
        JsonObject manifest = new JsonObject();
        JsonArray anchors = new JsonArray();
        for (OccurrenceAddress root : roots) anchors.add(root.render());
        manifest.add("anchors", anchors);
        manifest.addProperty("topologyEpoch", topologyEpoch);
        manifest.addProperty("wave", open.index);
        manifest.addProperty("state", open.empty()
                ? "FIXED_POINT" : "OBLIGATIONS_PROPOSED");
        manifest.addProperty("tasks", tasks.size());
        manifest.addProperty("proposed", open.obligations.size());
        manifest.addProperty("answered", frontier.answeredCount());
        JsonArray rows = new JsonArray();
        Map<String, int[]> perTask = frontier.perTask();
        for (Task task : tasks) {
            int[] counts = perTask.get(task.taskId());
            JsonObject row = new JsonObject();
            row.addProperty("taskId", task.taskId());
            row.addProperty("focused", task.focused().render());
            row.addProperty("factor", task.factor().size());
            row.addProperty("seedSessionId", task.seedSessionId());
            row.addProperty("proposed", counts == null ? 0 : counts[1]);
            rows.add(row);
        }
        manifest.add("taskRows", rows);
        JsonObject verdicts = new JsonObject();
        for (Map.Entry<String, Integer> entry
                : frontier.verdictHistogram().entrySet()) {
            verdicts.addProperty(entry.getKey(), entry.getValue());
        }
        manifest.add("verdicts", verdicts);
        JsonObject kinds = new JsonObject();
        Map<String, Integer> byKind = new LinkedHashMap<String, Integer>();
        for (GapRow gap : distinct(gaps)) {
            Integer count = byKind.get(gap.kind().name());
            byKind.put(gap.kind().name(), count == null ? 1 : count + 1);
        }
        for (Map.Entry<String, Integer> entry : byKind.entrySet()) {
            kinds.addProperty(entry.getKey(), entry.getValue());
        }
        manifest.add("gaps", kinds);
        return manifest;
    }

    /** The same gap said twice is one gap. */
    static List<GapRow> distinct(List<GapRow> gaps) {
        return new ArrayList<GapRow>(new LinkedHashSet<GapRow>(gaps));
    }

    static String pretty(JsonObject json) {
        return new GsonBuilder().disableHtmlEscaping().setPrettyPrinting()
                .create().toJson(json);
    }

    // ---- options ------------------------------------------------------

    static Map<String, String> options(String[] argv) {
        Map<String, String> options = new LinkedHashMap<String, String>();
        for (int index = 0; index < argv.length; index++) {
            String argument = argv[index];
            if (!argument.startsWith("--")) continue;
            String name = argument.substring(2);
            int equals = name.indexOf('=');
            if (equals >= 0) {
                options.put(name.substring(0, equals),
                        name.substring(equals + 1));
            } else if (index + 1 < argv.length
                    && !argv[index + 1].startsWith("--")) {
                options.put(name, argv[++index]);
            } else {
                options.put(name, "true");
            }
        }
        return options;
    }

    static String value(Map<String, String> options, String name,
                        String fallback) {
        String value = options.get(name);
        return value == null || value.trim().isEmpty() ? fallback : value;
    }

    static Path path(Map<String, String> options, String name) {
        String value = options.get(name);
        return value == null || value.trim().isEmpty()
                ? null : Paths.get(value);
    }

    static long number(Map<String, String> options, String name,
                       long fallback) {
        String value = options.get(name);
        if (value == null || value.trim().isEmpty()) return fallback;
        try {
            return Long.parseLong(value.trim());
        } catch (NumberFormatException notANumber) {
            return fallback;
        }
    }
}
