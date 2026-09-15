package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.plan.SelectorResolution;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.Selector;
import edu.uva.liftlab.graphchecker.contract.Task;

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
 *   --target-occurrence &lt;sel&gt;  the case's declared anchor, a v1 selector,
 *                              and the ONE root of the closure
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
    /** A task the anchor's closure holds: it opens slots and joins families. */
    static final String CLOSURE_MEMBER = "CLOSURE_MEMBER";
    /** A task because it decided something over a SYMBOL. */
    static final String SYMBOLIC_DECISION = "SYMBOLIC_DECISION";

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
        String declaredAnchor = value(options, "target-occurrence", "");
        if (declaredAnchor.isEmpty()) {
            throw new IllegalArgumentException("the closure has no root: "
                    + "pass --target-occurrence. A case declares ONE anchor "
                    + "(HANDOVER SS1.6) and the closure is that anchor's");
        }
        JsonObject manifest = plan(iteration, declaredAnchor,
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
     * @param declaredAnchor the case's own declaration, in the v1 spelling a
     *                       human writes, and the only root the closure has
     *                       (HANDOVER SS1.5).  It is resolved against the
     *                       seed session here, because a selector is not an
     *                       identity and nothing downstream may see one.
     */
    public static JsonObject plan(Path iteration, String declaredAnchor,
                                  Path rootDomains, Path results, Path out,
                                  int wave, String topologyEpoch,
                                  int maxTasks,
                                  ObligationFactory.Bounds bounds)
            throws IOException {
        Corpus corpus = Corpus.read(iteration, rootDomains);
        List<GapRow> gaps = new ArrayList<GapRow>();
        List<OccurrenceAddress> roots = resolve(corpus, declaredAnchor, gaps);
        List<Task> tasks = new ArrayList<Task>();
        Map<String, String> why = new LinkedHashMap<String, String>();
        Set<String> opened = new LinkedHashSet<String>();
        for (OccurrenceAddress root : roots) {
            ClosurePlanner.Plan plan = ClosurePlanner.plan(corpus, root,
                    maxTasks);
            gaps.addAll(plan.gaps);
            for (Task task : plan.tasks) {
                if (!opened.add(task.taskId())) continue;
                tasks.add(task);
                why.put(task.taskId(), CLOSURE_MEMBER);
            }
        }
        // The closure's own members, and nothing about slots or families,
        // come from the rows.  A decision that rests on a DECLARED root is a
        // flip candidate by definition -- the static graph's only job is to
        // decide what to track, branches to flip included -- and on 17960 no
        // row of the seed could ever put the deletion region in the anchor's
        // closure: the seed runs the marker's true arm, where deleteSnapshot
        // defers and the decrement never executes.  So those occurrences are
        // tasks too, and stay OUTSIDE the closure until their own rows
        // connect them (INTERACTION-ID SS8 case 1, which the next wave's
        // recomputation does by itself).
        Set<String> closure = closureOf(tasks);
        for (Task task : ClosurePlanner.symbolicDecision(corpus, opened)) {
            if (!opened.add(task.taskId())) continue;
            tasks.add(task);
            why.put(task.taskId(), SYMBOLIC_DECISION);
        }
        // The epoch's skeleton, reconciled against everything the replays
        // have said so far.  It is taken AFTER the closure is planned,
        // because a slot is opened only for an interaction whose consumer is
        // a closure member, and before the obligations, because a
        // replacement contradicts the skeleton the wave would be cut from.
        SlotTable slots = SlotTable.read(iteration);
        SlotTable.Reconciliation skeleton = slots.reconcile(corpus, closure,
                wave);
        gaps.addAll(skeleton.gaps);
        slots.write(iteration);

        Frontier frontier = new Frontier(tasks);
        frontier.consume(RowCodec.readAll(results,
                ExploreCodec::readResult));
        List<ObligationFactory.Candidate> candidates =
                new ArrayList<ObligationFactory.Candidate>();
        for (Task task : tasks) {
            candidates.addAll(ObligationFactory.candidates(corpus, task,
                    bounds, frontier::asked, gaps));
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
        JsonObject manifest = manifest(roots, tasks, why, frontier, open,
                topologyEpoch, gaps, slots, skeleton);
        Files.write(out.resolve("explore_manifest.json"),
                (pretty(manifest) + System.lineSeparator())
                        .getBytes(StandardCharsets.UTF_8));
        return manifest;
    }

    /**
     * Resolves the case's declared anchor against the seed's own activations.
     *
     * <p>Humans do not write execution indexes (IDENTITY-V3 SS2), and which
     * occurrence a case meant is one question with one answer:
     * {@link SelectorResolution} is that answer, for PLAN, for the composer
     * and for this stage. What is left here is what this stage does with an
     * unresolved one — refuse the wave, naming the selector and what the seed
     * session did run that region as, because the cause is nearly always a
     * spelling the case and the deployment do not share and no reader can see
     * that from "no tasks".</p>
     *
     * <p>A declaration already written as a full address resolves by PARSING
     * ({@link SelectorResolution} SS60), which asks the recording nothing: a
     * string is an address as soon as it is shaped like one. So every root is
     * checked here against the activations of the seed session, and one the
     * seed did not run is named and dropped rather than planned. The stage
     * cannot focus a replay on an occurrence no run recorded, and a task
     * carrying an empty {@code seedSessionId} is refused by the contract
     * (CONTRACT-SPEC SS3) far from where the address came from. Refusing it
     * is BLOCKING: the anchor is the closure's only root, so without it there
     * is no claim to make.</p>
     *
     * <p>The seed replay's task plan used to be a second source of roots, and
     * is not one: the closure is the ANCHOR's (HANDOVER SS1.5), and a plan
     * row is the PLAN side's own address for a region, which in the first
     * real 17960 corpus disagreed with the recording's for 43 of 45 rows.
     * What exploration needs to know about a region it cannot see inside is
     * whether the workload retained it, and the rows say that themselves
     * ({@code ActivationRow.instrumented}, INTERACTION-ID SS8 case 2, read in
     * {@link SlotTable}).</p>
     */
    private static List<OccurrenceAddress> resolve(Corpus corpus,
                                                   String declaredAnchor,
                                                   List<GapRow> gaps) {
        String seed = corpus.seedSessionId();
        if (seed.isEmpty()) {
            // The contract's rule, and no fallback under it: the seed is the
            // session that focused nothing, and a corpus with none of those
            // or with several does not state which recording a declaration
            // was written about. Naming an exploration replay as the
            // recording is how a claim comes to be about the wrong execution.
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION, GapKind.ADMISSION_GAP, GapClass.BLOCKING,
                    declaredAnchor,
                    "this corpus states no single seed session: "
                            + corpus.unfocusedSessionIds().size()
                            + " of its " + corpus.sessions().size()
                            + " sessions focused nothing"));
            return new ArrayList<OccurrenceAddress>();
        }
        SessionReader session = corpus.session(seed);
        List<ActivationRow> activations = session == null
                ? new ArrayList<ActivationRow>() : session.activations();
        Set<String> ranInTheSeed = new LinkedHashSet<String>();
        for (ActivationRow activation : activations) {
            ranInTheSeed.add(activation.occurrence().id());
        }
        List<OccurrenceAddress> roots = new ArrayList<OccurrenceAddress>();
        OccurrenceAddress anchor = root(declaredAnchor, seed, activations,
                ranInTheSeed, GapClass.BLOCKING, gaps);
        if (anchor != null) roots.add(anchor);
        return roots;
    }

    /** The declaration's occurrence, or null with the refusal named. */
    private static OccurrenceAddress root(String declared, String seed,
                                          List<ActivationRow> activations,
                                          Set<String> ranInTheSeed,
                                          GapClass cls, List<GapRow> gaps) {
        OccurrenceAddress match;
        try {
            match = SelectorResolution.resolve(declared, activations);
        } catch (IllegalArgumentException malformed) {
            gaps.add(GapRow.of(seed, GapKind.DECLARATION_MISSING, cls,
                    declared,
                    "not a case selector: " + malformed.getMessage()));
            return null;
        }
        if (SelectorResolution.unresolved(match)) {
            gaps.add(GapRow.of(seed, GapKind.ADMISSION_GAP, cls, declared,
                    "no occurrence of the seed session " + seed
                            + " matches it; that region ran as: "
                            + offered(declared, activations)));
            return null;
        }
        if (!ranInTheSeed.contains(match.id())) {
            gaps.add(GapRow.of(seed, GapKind.ADMISSION_GAP, cls,
                    match.render(),
                    "this address is shaped like an occurrence but the seed "
                            + "session " + seed + " published no activation "
                            + "for it, so no replay can be focused on it; "
                            + "region " + match.regionId() + " ran there as: "
                            + ofRegion(match.regionId(), activations)));
            return null;
        }
        return match;
    }

    /** What the seed session ran that region as, for a refusal to name. */
    private static String offered(String declared,
                                  List<ActivationRow> seed) {
        Selector selector;
        try {
            selector = OccurrenceAddress.parseSelector(declared);
        } catch (IllegalArgumentException notASelector) {
            return "(not a selector)";
        }
        return ofRegion(selector.regionId(), seed);
    }

    /** The contexts one region ran under in the seed, at most four. */
    private static String ofRegion(String regionId,
                                   List<ActivationRow> seed) {
        List<String> named = new ArrayList<String>();
        for (ActivationRow activation : seed) {
            OccurrenceAddress occurrence = activation.occurrence();
            if (!regionId.equals(occurrence.regionId())) continue;
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
                                       List<Task> tasks,
                                       Map<String, String> why,
                                       Frontier frontier,
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
            // Why this occurrence is a task at all: a reader of the manifest
            // must not have to re-derive the closure to find out.
            row.addProperty("why", why.get(task.taskId()));
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
