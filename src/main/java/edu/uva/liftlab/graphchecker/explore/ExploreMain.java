package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.plan.SelectorResolution;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.Selector;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.option.LongOptions;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
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
 *   --sessions &lt;dir&gt;           the corpus; its parent is the iteration
 *   --target-occurrence &lt;sel&gt;  the case's declared anchor (v1 selector),
 *                              the ONE root of the closure
 *   --results &lt;file&gt;           earlier waves' ObligationResults; an
 *                              answered query is never proposed again
 *   --static-scope-map &lt;file&gt;  the epoch's write/export sites and guards
 *                              (CLOSURE-V2 SS4)
 *   --root-domains &lt;file&gt;      what the CASE says each root may be
 *   --wave &lt;n&gt;                 which wave this is
 *   --topology-epoch &lt;id&gt;      the epoch these sessions belong to
 *   --output-dir &lt;dir&gt;         obligations.jsonl, tasks.jsonl, gaps.jsonl,
 *                              graph.jsonl, growth.jsonl,
 *                              explore_manifest.json
 *   --max-tasks / --max-paths-per-region / --max-flips-per-path /
 *   --max-world-depth
 * </pre>
 *
 * <p>ONE invocation is ONE wave; the campaign owns the loop and the workers.
 * This rebuilds the frontier from every session and recorded verdict and writes
 * the unanswered flips. It never solves ({@link ObligationSolverMain} does, one
 * worker per obligation).</p>
 */
public final class ExploreMain {
    private ExploreMain() {
    }

    public static void main(String[] argv) throws Exception {
        LongOptions options = LongOptions.parse(argv);
        // The iteration is the parent of --sessions.
        Path sessions = options.path("sessions");
        if (sessions == null) {
            throw new IllegalArgumentException("Missing --sessions");
        }
        Path iteration = sessions.getParent() == null
                ? sessions : sessions.getParent();
        Path out = options.path("output-dir");
        if (out == null) {
            throw new IllegalArgumentException("Missing --output-dir");
        }
        String declaredAnchor = options.value("target-occurrence", "");
        if (declaredAnchor.isEmpty()) {
            throw new IllegalArgumentException("the closure has no root: "
                    + "pass --target-occurrence. A case declares ONE anchor "
                    + "(HANDOVER SS1.6) and the closure is that anchor's");
        }
        // Fail-closed: without the map the closure is the rows' alone, which
        // can miss the writer region the failure depends on (CLOSURE-V2 SS2).
        Path scopeMap = options.path("static-scope-map");
        if (scopeMap == null) {
            throw new IllegalArgumentException("the closure has no static "
                    + "map: pass --static-scope-map. PLAN publishes "
                    + StaticScopeMap.FILE + " per epoch, and the closure "
                    + "needs it to name the writers a replay has not run "
                    + "(CLOSURE-V2 SS2)");
        }
        JsonObject manifest = plan(iteration, declaredAnchor,
                options.path("root-domains"), options.path("results"),
                scopeMap, out,
                (int) options.number("wave", 0),
                options.value("topology-epoch", ""),
                (int) options.number("max-tasks",
                        ClosurePlanner.DEFAULT_MAX_TASKS),
                new ObligationFactory.Bounds(
                        (int) options.number("max-paths-per-region",
                                ObligationFactory.DEFAULT_MAX_PATHS_PER_TASK),
                        (int) options.number("max-flips-per-path",
                                ObligationFactory.DEFAULT_MAX_FLIPS_PER_PATH),
                        (int) options.number("max-world-depth",
                                ObligationFactory.DEFAULT_MAX_WORLD_DEPTH)));
        System.out.println(pretty(manifest));
    }

    /**
     * Plans one wave.
     *
     * @param declaredAnchor the case's v1 declaration,
     *                       the closure's only root (HANDOVER SS1.5); resolved
     *                       against the seed here, so nothing downstream sees a
     *                       selector
     */
    public static JsonObject plan(Path iteration, String declaredAnchor,
                                  Path rootDomains, Path results,
                                  Path scopeMap, Path out,
                                  int wave, String topologyEpoch,
                                  int maxTasks,
                                  ObligationFactory.Bounds bounds)
            throws IOException {
        Corpus corpus = Corpus.read(iteration, rootDomains);
        StaticScopeMap scope = StaticScopeMap.read(scopeMap);
        List<GapRow> gaps = new ArrayList<GapRow>();
        gaps.addAll(unstableAddresses(corpus));
        List<OccurrenceAddress> roots = resolve(corpus, declaredAnchor, gaps);
        List<Task> tasks = new ArrayList<Task>();
        Map<String, String> why = new LinkedHashMap<String, String>();
        Map<String, Set<String>> flipSites =
                new LinkedHashMap<String, Set<String>>();
        Set<String> opened = new LinkedHashSet<String>();
        for (OccurrenceAddress root : roots) {
            ClosurePlanner.Plan plan = ClosurePlanner.plan(corpus, root,
                    maxTasks, scope);
            gaps.addAll(plan.gaps);
            for (Task task : plan.tasks) {
                if (!opened.add(task.taskId())) continue;
                tasks.add(task);
                why.put(task.taskId(), plan.why.get(task.taskId()));
                flipSites.put(task.taskId(),
                        plan.flipSites.get(task.taskId()));
            }
        }
        Set<String> closure = closureOf(tasks);
        // Reconcile the skeleton; a same-world replacement is BLOCKING but
        // never empties the wave (DESIGN4 SS3.3c).
        SlotTable slots = SlotTable.read(iteration);
        SlotTable.Reconciliation skeleton = slots.reconcile(corpus, closure,
                wave);
        gaps.addAll(skeleton.gaps);
        slots.write(iteration);

        // The one ledger of owed arms (Frontier).
        Frontier frontier = new Frontier(corpus, tasks);
        frontier.consume(RowCodec.readAll(results,
                RowCodec::readObligationResult));
        List<ObligationFactory.Candidate> candidates =
                new ArrayList<ObligationFactory.Candidate>();
        for (Task task : tasks) {
            candidates.addAll(ObligationFactory.candidates(corpus, task,
                    flipSites.get(task.taskId()), bounds, frontier, gaps));
        }
        Frontier.Wave open = frontier.open(wave, candidates);

        Files.createDirectories(out);
        // G_k and growth (DESIGN4 SS3); empty growth.jsonl + obligations.jsonl
        // is the driver's fixed point.
        WaveGraph.of(corpus).write(out, wave);
        int exposed = WaveGraph.writeGrowth(corpus, anchorTask(roots, tasks),
                out, gaps);
        RowCodec.writeAll(out.resolve("tasks.jsonl"), tasks,
                ExploreCodec::writeTask);
        // An empty file IS the frontier closing.
        RowCodec.writeAll(out.resolve("obligations.jsonl"), open.obligations,
                ExploreCodec::writeObligation);
        RowCodec.writeAll(out.resolve("gaps.jsonl"), distinct(gaps),
                RowCodec::writeGap);
        JsonObject manifest = manifest(roots, tasks, why, frontier, open,
                topologyEpoch, gaps, slots, skeleton, exposed);
        Files.write(out.resolve("explore_manifest.json"),
                (pretty(manifest) + System.lineSeparator())
                        .getBytes(StandardCharsets.UTF_8));
        return manifest;
    }

    /** Planned tasks answered at more than ONE address across replays. The
     *  ledger keys arms by address ({@link ClosurePlanner#taskId}), so a moving
     *  address re-asks settled arms forever; the cause is upstream ({@code
     *  runtime.Identity}). DIAGNOSTIC: exploration still proceeds. */
    private static List<GapRow> unstableAddresses(Corpus corpus) {
        Map<String, Map<String, String>> answeredBy =
                new LinkedHashMap<String, Map<String, String>>();
        for (SessionReader session : corpus.sessions()) {
            for (ActivationRow activation : session.activations()) {
                if (activation.taskId().isEmpty()) continue;
                answeredBy.computeIfAbsent(activation.taskId(),
                        key -> new LinkedHashMap<String, String>())
                        .putIfAbsent(activation.occurrence().render(),
                                session.sessionId());
            }
        }
        List<GapRow> unstable = new ArrayList<GapRow>();
        for (Map.Entry<String, Map<String, String>> answered
                : answeredBy.entrySet()) {
            if (answered.getValue().size() < 2) continue;
            List<String> named = new ArrayList<String>();
            for (Map.Entry<String, String> address
                    : answered.getValue().entrySet()) {
                named.add(address.getKey() + " (first in session "
                        + address.getValue() + ")");
            }
            unstable.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADDRESS_UNSTABLE, GapClass.DIAGNOSTIC,
                    answered.getKey(),
                    "this planned task was answered at "
                            + answered.getValue().size()
                            + " addresses across " + corpus.sessions().size()
                            + " sessions, so an arm answered at one of them "
                            + "is owed again at the others: "
                            + String.join(" | ", named)));
        }
        return unstable;
    }

    /**
     * Resolves the declared anchor via {@link SelectorResolution} (IDENTITY-V3
     * SS2) and refuses the wave, BLOCKING, when it does not resolve -- naming
     * what the seed ran that region as, since the cause is usually a spelling
     * mismatch. A full address resolves by parsing alone, so it is also checked
     * against the seed's activations: no replay can focus an occurrence no run
     * recorded (CONTRACT-SPEC SS3). The closure is the ANCHOR's only (HANDOVER
     * SS1.5); plan rows are not roots.
     */
    private static List<OccurrenceAddress> resolve(Corpus corpus,
                                                   String declaredAnchor,
                                                   List<GapRow> gaps) {
        String seed = corpus.seedSessionId();
        if (seed.isEmpty()) {
            // Exactly one SEED-role session, no fallback: another would make
            // the claim about the wrong execution.
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION, GapKind.ADMISSION_GAP, GapClass.BLOCKING,
                    declaredAnchor,
                    "this corpus states no single seed session: "
                            + corpus.seedSessionIds().size()
                            + " of its " + corpus.sessions().size()
                            + " sessions state role SEED"));
            return new ArrayList<OccurrenceAddress>();
        }
        List<ActivationRow> activations = corpus.session(seed).activations();
        Set<String> ranInTheSeed = new LinkedHashSet<String>();
        for (ActivationRow activation : activations) {
            ranInTheSeed.add(activation.occurrence().id());
        }
        List<OccurrenceAddress> roots = new ArrayList<OccurrenceAddress>();
        OccurrenceAddress anchor = root(declaredAnchor, seed, activations,
                ranInTheSeed, gaps);
        if (anchor != null) roots.add(anchor);
        return roots;
    }

    /** The declaration's occurrence, or null with the BLOCKING refusal named.
     */
    private static OccurrenceAddress root(String declared, String seed,
                                          List<ActivationRow> activations,
                                          Set<String> ranInTheSeed,
                                          List<GapRow> gaps) {
        GapClass cls = GapClass.BLOCKING;
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

    /** The anchor's own task, or null when the anchor opened none. */
    private static Task anchorTask(List<OccurrenceAddress> roots,
                                   List<Task> tasks) {
        for (Task task : tasks) {
            if (roots.contains(task.focused())) return task;
        }
        return null;
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
                                       SlotTable.Reconciliation skeleton,
                                       int exposed) {
        JsonObject manifest = new JsonObject();
        JsonArray anchors = new JsonArray();
        for (OccurrenceAddress root : roots) anchors.add(root.render());
        manifest.add("anchors", anchors);
        manifest.addProperty("topologyEpoch", topologyEpoch);
        manifest.addProperty("wave", open.index);
        manifest.addProperty("state",
                open.empty() ? "FIXED_POINT" : "OBLIGATIONS_PROPOSED");
        manifest.addProperty("exposedRegions", exposed);
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
        Map<String, Integer> proposedPerTask = frontier.proposedPerTask();
        for (Task task : tasks) {
            Integer proposedHere = proposedPerTask.get(task.taskId());
            JsonObject row = new JsonObject();
            row.addProperty("taskId", task.taskId());
            row.addProperty("focused", task.focused().render());
            row.addProperty("factor", task.factor().size());
            row.addProperty("seedSessionId", task.seedSessionId());
            // Why this occurrence is a task, so readers need not re-derive the
            // closure.
            row.addProperty("why", why.get(task.taskId()));
            row.addProperty("proposed", proposedHere == null ? 0 : proposedHere);
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
            byKind.merge(gap.kind().name(), 1, Integer::sum);
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
}
