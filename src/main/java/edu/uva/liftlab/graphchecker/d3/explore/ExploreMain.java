package edu.uva.liftlab.graphchecker.d3.explore;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.d3.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.d3.contract.CausalContext;
import edu.uva.liftlab.graphchecker.d3.contract.GapClass;
import edu.uva.liftlab.graphchecker.d3.contract.GapKind;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.SessionReader;
import edu.uva.liftlab.graphchecker.d3.contract.Selector;
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
 *   --task-plan &lt;file&gt;         the seed replay's plan; its occurrenceIds are
 *                              selectors too, resolved the same way
 *   --target-occurrence &lt;sel&gt;  the case's declared anchor, a v1 selector
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
    /** What tells a resolved occurrence id from a case's v1 selector. */
    private static final String RESOLVED_MARKER = "/ctx:";

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
        JsonObject manifest = plan(iteration, selectors(options),
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
     * @param selectors what the case declares, in the v1 spelling: the
     *                  declared anchor and the seed plan's own occurrences.
     *                  They are resolved against the seed session here,
     *                  because a selector is not an identity and nothing
     *                  downstream may see one.
     */
    public static JsonObject plan(Path iteration, List<String> selectors,
                                  Path rootDomains, Path results, Path out,
                                  int wave, String topologyEpoch,
                                  int maxTasks,
                                  ObligationFactory.Bounds bounds)
            throws IOException {
        Corpus corpus = Corpus.read(iteration, rootDomains);
        List<GapRow> gaps = new ArrayList<GapRow>();
        List<OccurrenceAddress> roots = resolve(corpus, selectors, gaps);
        List<Task> tasks = new ArrayList<Task>();
        Set<String> planned = new LinkedHashSet<String>();
        for (OccurrenceAddress root : roots) {
            ClosurePlanner.Plan plan = ClosurePlanner.plan(corpus, root,
                    maxTasks);
            gaps.addAll(plan.gaps);
            for (Task task : plan.tasks) {
                if (planned.add(task.taskId())) tasks.add(task);
            }
        }
        // The epoch's skeleton, reconciled against everything the replays
        // have said so far.  It is taken AFTER the closure is planned,
        // because a slot is opened only for an interaction whose consumer is
        // a closure member, and before the obligations, because a
        // replacement contradicts the skeleton the wave would be cut from.
        SlotTable slots = SlotTable.read(iteration);
        SlotTable.Reconciliation skeleton = slots.reconcile(corpus,
                closureOf(tasks), wave);
        gaps.addAll(skeleton.gaps);
        slots.write(iteration);

        Frontier frontier = new Frontier(tasks);
        frontier.consume(RowCodec.readAll(results,
                ExploreCodec::readResult));
        List<ObligationFactory.Candidate> candidates =
                new ArrayList<ObligationFactory.Candidate>();
        for (Task task : tasks) {
            candidates.addAll(ObligationFactory.candidates(corpus, task,
                    bounds, frontier::asked));
        }
        Frontier.Wave open = skeleton.replaced
                ? frontier.open(wave,
                        new ArrayList<ObligationFactory.Candidate>())
                : frontier.open(wave, candidates);

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
                topologyEpoch, gaps, slots, skeleton);
        Files.write(out.resolve("explore_manifest.json"),
                (pretty(manifest) + System.lineSeparator())
                        .getBytes(StandardCharsets.UTF_8));
        return manifest;
    }

    /** What the case declares, in the v1 spelling: anchor, then the plan's. */
    private static List<String> selectors(Map<String, String> options)
            throws IOException {
        List<String> selectors = new ArrayList<String>();
        String declared = value(options, "target-occurrence", "");
        if (!declared.isEmpty()) selectors.add(declared);
        Path plan = path(options, "task-plan");
        if (plan != null && Files.isRegularFile(plan)) {
            for (JsonObject row : RowCodec.readJsonl(plan)) {
                JsonElement occurrence = row.get("occurrenceId");
                if (occurrence == null || !occurrence.isJsonPrimitive()) {
                    continue;
                }
                String text = occurrence.getAsString();
                if (!selectors.contains(text)) selectors.add(text);
            }
        }
        if (selectors.isEmpty()) {
            throw new IllegalArgumentException("the closure has no root: "
                    + "pass --target-occurrence, or a --task-plan whose rows "
                    + "name an occurrenceId");
        }
        return selectors;
    }

    /**
     * Resolves each declared selector against the seed session.
     *
     * <p>Humans do not write execution indexes (IDENTITY-V3 SS2): a case
     * declares a SELECTOR -- node, region, the api that started the
     * occurrence when one is given, and which match -- and the seed session's
     * own activation order decides which occurrence that is.  The resolved id
     * is what exploration and composition use; a selector never leaves this
     * method.</p>
     *
     * <p>A selector nothing matches is an {@code ADMISSION_GAP} naming it and
     * what the seed session did offer for that region, because the reason is
     * almost always a spelling the deployment and the case do not share, and
     * a reader cannot see that from "no tasks".</p>
     */
    private static List<OccurrenceAddress> resolve(Corpus corpus,
                                                   List<String> selectors,
                                                   List<GapRow> gaps) {
        String seed = corpus.seedSessionId();
        if (seed.isEmpty()) {
            // The contract's rule, and no fallback under it: the seed is the
            // session that focused nothing, and a corpus with none of those
            // or with several does not state which recording a declaration
            // was written about.  Naming an exploration replay as the
            // recording is how a claim comes to be about the wrong execution.
            gaps.add(GapRow.of("", GapKind.ADMISSION_GAP, GapClass.BLOCKING,
                    String.join(", ", selectors),
                    "this corpus states no single seed session: "
                            + corpus.unfocusedSessionIds().size()
                            + " of its " + corpus.sessions().size()
                            + " sessions focused nothing"));
            return new ArrayList<OccurrenceAddress>();
        }
        List<OccurrenceAddress> occurrences = seedOccurrences(corpus, seed);
        String scope = "the seed session " + seed;
        List<OccurrenceAddress> roots = new ArrayList<OccurrenceAddress>();
        Set<String> resolved = new LinkedHashSet<String>();
        for (String text : selectors) {
            if (text.contains(RESOLVED_MARKER)) {
                // Already an id: the scheduler resolved it, or a re-run
                // passed back what an earlier manifest published.
                try {
                    OccurrenceAddress address = OccurrenceAddress.parse(text);
                    if (resolved.add(address.id())) roots.add(address);
                    continue;
                } catch (IllegalArgumentException malformed) {
                    gaps.add(GapRow.of(seed, GapKind.DECLARATION_MISSING,
                            GapClass.BLOCKING, text,
                            "not an occurrence id: "
                                    + malformed.getMessage()));
                    continue;
                }
            }
            Selector selector;
            try {
                selector = OccurrenceAddress.parseSelector(text);
            } catch (IllegalArgumentException malformed) {
                gaps.add(GapRow.of(seed, GapKind.DECLARATION_MISSING,
                        GapClass.BLOCKING, text,
                        "not a case selector: " + malformed.getMessage()));
                continue;
            }
            OccurrenceAddress match = match(selector, occurrences);
            if (match == null) {
                gaps.add(GapRow.of(seed, GapKind.ADMISSION_GAP,
                        GapClass.BLOCKING, selector.render(),
                        "no occurrence of " + scope + " matches it; that "
                                + "region ran as: "
                                + offered(selector, occurrences)));
                continue;
            }
            if (resolved.add(match.id())) roots.add(match);
        }
        return roots;
    }

    /** The k-th occurrence this selector matches, in the seed's own order. */
    private static OccurrenceAddress match(Selector selector,
                                           List<OccurrenceAddress> seed) {
        int matched = 0;
        for (OccurrenceAddress occurrence : seed) {
            if (!selector.matches(occurrence, apiOf(selector, occurrence))) {
                continue;
            }
            if (++matched == selector.k()) return occurrence;
        }
        return null;
    }

    /**
     * The api of the message that started this occurrence, or "".
     *
     * <p>The contract will not guess an api out of a deployment's RPC static
     * site spelling, and it is right not to; this is the rule for the one
     * spelling the cases meet, and it is the composer's rule verbatim, so
     * that one declaration elects one occurrence in both stages.  A v1
     * declaration writes the api as the tail of the source it came from, so
     * the two are compared on their last path segment; an exact site
     * spelling still matches itself.</p>
     */
    private static String apiOf(Selector selector,
                                OccurrenceAddress occurrence) {
        if (occurrence.context().form() != CausalContext.Form.ANCHOR) {
            return "";
        }
        String site = ((CausalContext.Anchor) occurrence.context()).rpcSite();
        if (selector.api() == null) return site;
        // Answer the selector's own spelling where the two name one api, so
        // that the contract's equality decides and this rule only says which
        // spellings are the same api.
        return sameApi(selector.api(), site) ? selector.api() : site;
    }

    private static boolean sameApi(String declared, String site) {
        if (declared.equals(site)) return true;
        String left = tail(declared);
        String right = tail(site);
        return !left.isEmpty() && left.equals(right);
    }

    private static String tail(String value) {
        int slash = value.lastIndexOf('/');
        return slash < 0 ? value : value.substring(slash + 1);
    }

    /** What the seed session ran that region as, for a refusal to name. */
    private static String offered(Selector selector,
                                  List<OccurrenceAddress> seed) {
        List<String> named = new ArrayList<String>();
        for (OccurrenceAddress occurrence : seed) {
            if (!selector.regionId().equals(occurrence.regionId())) continue;
            if (named.size() >= 4) {
                named.add("...");
                break;
            }
            named.add(occurrence.node().render() + " "
                    + occurrence.context().render());
        }
        return named.isEmpty() ? "(that region ran there not at all)"
                : String.join(", ", named);
    }

    /** The seed session's occurrences, in the order it activated them. */
    private static List<OccurrenceAddress> seedOccurrences(Corpus corpus,
                                                           String seed) {
        List<OccurrenceAddress> occurrences =
                new ArrayList<OccurrenceAddress>();
        Set<String> seen = new LinkedHashSet<String>();
        SessionReader session = corpus.session(seed);
        if (session == null) return occurrences;
        for (ActivationRow activation : session.activations()) {
            if (seen.add(activation.occurrence().id())) {
                occurrences.add(activation.occurrence());
            }
        }
        return occurrences;
    }

    /** Every occurrence this wave's tasks hold: focused, and their factors. */
    private static Set<String> closureOf(List<Task> tasks) {
        Set<String> closure = new LinkedHashSet<String>();
        for (Task task : tasks) {
            closure.add(task.focused().id());
            for (OccurrenceAddress member : task.factor()) {
                closure.add(member.id());
            }
        }
        return closure;
    }

    private static JsonObject manifest(List<OccurrenceAddress> roots,
                                       List<Task> tasks, Frontier frontier,
                                       Frontier.Wave open,
                                       String topologyEpoch,
                                       List<GapRow> gaps, SlotTable slots,
                                       SlotTable.Reconciliation skeleton) {
        JsonObject manifest = new JsonObject();
        JsonArray anchors = new JsonArray();
        for (OccurrenceAddress root : roots) anchors.add(root.render());
        manifest.add("anchors", anchors);
        manifest.addProperty("topologyEpoch", topologyEpoch);
        manifest.addProperty("wave", open.index);
        manifest.addProperty("state", skeleton.replaced
                ? "TOPOLOGY_DIVERGENCE"
                : open.empty() ? "FIXED_POINT" : "OBLIGATIONS_PROPOSED");
        JsonObject skeletonRow = new JsonObject();
        skeletonRow.addProperty("slots", slots.size());
        skeletonRow.addProperty("opened", skeleton.opened.size());
        skeletonRow.addProperty("filled", skeleton.filled);
        skeletonRow.addProperty("outsideTheClosure", skeleton.outside);
        skeletonRow.addProperty("replaced", skeleton.replaced);
        manifest.add("skeleton", skeletonRow);
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
