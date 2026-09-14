package edu.uva.liftlab.graphchecker.d3.explore;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.Obligation;
import edu.uva.liftlab.graphchecker.d3.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.Task;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

/**
 * The EXPLORE stage: plan the anchor's closure, then run waves against it.
 *
 * <pre>
 *   --iteration &lt;dir&gt;            the corpus: &lt;dir&gt;/sessions/&lt;sessionId&gt;/...
 *   --target-occurrence &lt;addr&gt;   the declared anchor (v2 or either v1 form)
 *   --root-domains &lt;file&gt;        what the case declares its roots may be
 *   --max-waves N                the wave budget
 *   --out &lt;dir&gt;                  tasks.jsonl, wave-NNNN/obligations.jsonl
 * </pre>
 *
 * <p>One invocation plans every wave it can: it writes a wave's obligations,
 * and if the runtime has already written that wave's {@code results.jsonl} it
 * consumes them, re-reads the corpus (a VALIDATED replay published a session)
 * and plans the next.  It stops at {@code PENDING_RESULTS} when a wave is
 * waiting to be run, at {@code FIXED_POINT} when no task has a pending
 * obligation and no new one is offered, or at {@code MAX_WAVES}.  Re-invoking
 * it after the runtime has run a wave continues from the files, so the stage
 * is resumable and the engine drives it in a loop.</p>
 */
public final class ExploreMain {
    private static final String OBLIGATIONS = "obligations.jsonl";
    private static final String RESULTS = "results.jsonl";
    private static final String CLOSED = "closed.jsonl";
    private static final String GAPS = "gaps.jsonl";

    private ExploreMain() {
    }

    public static void main(String[] argv) throws Exception {
        Map<String, String> options = options(argv);
        JsonObject manifest = run(
                Paths.get(required(options, "iteration")),
                OccurrenceAddress.parse(required(options, "target-occurrence")),
                path(options, "root-domains"),
                Paths.get(required(options, "out")),
                (int) number(options, "max-waves", 8),
                Paths.get(value(options, "z3", "z3")),
                number(options, "solver-timeout-ms",
                        ObligationFactory.DEFAULT_TIMEOUT_MILLIS),
                (int) number(options, "max-tasks",
                        ClosurePlanner.DEFAULT_MAX_TASKS),
                (int) number(options, "max-obligations-per-task",
                        ObligationFactory.DEFAULT_MAX_PER_TASK),
                (int) number(options, "solver-threads",
                        ObligationFactory.DEFAULT_SOLVER_THREADS));
        System.out.println(new GsonBuilder().disableHtmlEscaping()
                .setPrettyPrinting().create().toJson(manifest));
    }

    /** Plans the closure and runs every wave the corpus already answers. */
    public static JsonObject run(Path iteration, OccurrenceAddress anchor,
                                 Path rootDomains, Path out, int maxWaves,
                                 Path z3, long timeoutMillis, int maxTasks,
                                 int maxPerTask) throws IOException {
        return run(iteration, anchor, rootDomains, out, maxWaves, z3,
                timeoutMillis, maxTasks, maxPerTask,
                ObligationFactory.DEFAULT_SOLVER_THREADS);
    }

    /** As above, solving each task's candidate flips {@code threads} at a time. */
    public static JsonObject run(Path iteration, OccurrenceAddress anchor,
                                 Path rootDomains, Path out, int maxWaves,
                                 Path z3, long timeoutMillis, int maxTasks,
                                 int maxPerTask, int threads)
            throws IOException {
        Corpus corpus = Corpus.read(iteration, rootDomains);
        ClosurePlanner.Plan plan = ClosurePlanner.plan(corpus, anchor,
                maxTasks);
        Files.createDirectories(out);
        RowCodec.writeAll(out.resolve("tasks.jsonl"), plan.tasks,
                ExploreCodec::writeTask);
        List<GapRow> gaps = new ArrayList<GapRow>(plan.gaps);
        Frontier frontier = new Frontier(plan.tasks);
        String state = "FIXED_POINT";
        int wave = 0;
        for (; wave < maxWaves; wave++) {
            Path directory = out.resolve(String.format("wave-%04d", wave));
            Path obligations = directory.resolve(OBLIGATIONS);
            Path results = directory.resolve(RESULTS);
            if (Files.isRegularFile(obligations)) {
                frontier.restore(RowCodec.readAll(obligations,
                                ExploreCodec::readObligation),
                        RowCodec.readAll(results, ExploreCodec::readResult));
                frontier.consume(RowCodec.readAll(directory.resolve(CLOSED),
                        ExploreCodec::readResult));
                if (!Files.isRegularFile(results)) {
                    state = "PENDING_RESULTS";
                    break;
                }
                corpus = Corpus.read(iteration, rootDomains);
                continue;
            }
            ObligationFactory factory = new ObligationFactory(corpus, z3,
                    timeoutMillis, maxPerTask, threads);
            List<ObligationFactory.Outcome> outcomes =
                    new ArrayList<ObligationFactory.Outcome>();
            for (Task task : plan.tasks) {
                outcomes.addAll(factory.obligations(task, frontier::asked));
            }
            Frontier.Wave issued = frontier.open(wave, outcomes);
            gaps.addAll(issued.gaps);
            if (issued.empty()) {
                state = "FIXED_POINT";
                break;
            }
            publish(directory, issued, outcomes);
            if (issued.obligations.isEmpty()) {
                // Every flip of this wave was closed here; nothing to run,
                // so the next wave can be planned at once.
                continue;
            }
            state = "PENDING_RESULTS";
            break;
        }
        if (wave >= maxWaves) state = "MAX_WAVES";
        RowCodec.writeAll(out.resolve(GAPS), distinct(gaps),
                RowCodec::writeGap);
        JsonObject manifest = manifest(anchor, plan, frontier, state, wave,
                gaps);
        Files.write(out.resolve("explore_manifest.json"),
                (new GsonBuilder().disableHtmlEscaping().setPrettyPrinting()
                        .create().toJson(manifest) + System.lineSeparator())
                        .getBytes(StandardCharsets.UTF_8));
        return manifest;
    }

    /** One wave on disk: what to run, what closed, and every query's text. */
    private static void publish(Path directory, Frontier.Wave wave,
                                List<ObligationFactory.Outcome> outcomes)
            throws IOException {
        Files.createDirectories(directory);
        RowCodec.writeAll(directory.resolve(OBLIGATIONS), wave.obligations,
                ExploreCodec::writeObligation);
        RowCodec.writeAll(directory.resolve(CLOSED), wave.closed,
                ExploreCodec::writeResult);
        RowCodec.writeAll(directory.resolve(GAPS), distinct(wave.gaps),
                RowCodec::writeGap);
        if (wave.obligations.isEmpty()) {
            // Nothing for the runtime to run, so this wave's results are
            // complete as they stand: say so, or resuming would wait for a
            // file nobody is going to write.
            RowCodec.writeAll(directory.resolve(RESULTS),
                    Collections.<ObligationResult>emptyList(),
                    ExploreCodec::writeResult);
        }
        Path queries = directory.resolve("smt");
        Files.createDirectories(queries);
        for (ObligationFactory.Outcome outcome : outcomes) {
            if (outcome.smt2.isEmpty()) continue;
            Files.write(queries.resolve(outcome.obligationId + ".smt2"),
                    outcome.smt2.getBytes(StandardCharsets.UTF_8));
        }
    }

    private static JsonObject manifest(OccurrenceAddress anchor,
                                       ClosurePlanner.Plan plan,
                                       Frontier frontier, String state,
                                       int wave, List<GapRow> gaps) {
        JsonObject manifest = new JsonObject();
        manifest.addProperty("anchor", anchor.render());
        manifest.addProperty("state", state);
        manifest.addProperty("wave", wave);
        manifest.addProperty("tasks", plan.tasks.size());
        manifest.addProperty("pending", frontier.pending().size());
        JsonArray tasks = new JsonArray();
        Map<String, int[]> perTask = frontier.perTask();
        for (Task task : plan.tasks) {
            int[] counts = perTask.get(task.taskId());
            JsonObject row = new JsonObject();
            row.addProperty("taskId", task.taskId());
            row.addProperty("focused", task.focused().render());
            row.addProperty("factor", task.factor().size());
            row.addProperty("seedSessionId", task.seedSessionId());
            row.addProperty("asked", counts == null ? 0 : counts[0]);
            row.addProperty("pending", counts == null ? 0 : counts[1]);
            tasks.add(row);
        }
        manifest.add("taskRows", tasks);
        JsonObject verdicts = new JsonObject();
        for (Map.Entry<String, Integer> entry
                : frontier.verdictHistogram().entrySet()) {
            verdicts.addProperty(entry.getKey(), entry.getValue());
        }
        manifest.add("verdicts", verdicts);
        JsonObject kinds = new JsonObject();
        Map<String, Integer> byKind = new LinkedHashMap<String, Integer>();
        for (GapRow gap : gaps) {
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
    private static List<GapRow> distinct(List<GapRow> gaps) {
        return new ArrayList<GapRow>(new LinkedHashSet<GapRow>(gaps));
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

    private static String required(Map<String, String> options, String name) {
        String value = options.get(name);
        if (value == null || value.trim().isEmpty()) {
            throw new IllegalArgumentException("Missing --" + name);
        }
        return value;
    }

    private static String value(Map<String, String> options, String name,
                                String fallback) {
        String value = options.get(name);
        return value == null || value.trim().isEmpty() ? fallback : value;
    }

    private static Path path(Map<String, String> options, String name) {
        String value = options.get(name);
        return value == null || value.trim().isEmpty()
                ? null : Paths.get(value);
    }

    private static long number(Map<String, String> options, String name,
                               long fallback) {
        String value = options.get(name);
        return value == null || value.trim().isEmpty()
                ? fallback : Long.parseLong(value.trim());
    }
}
