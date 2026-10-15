package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.plan.SelectorResolution;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.Selector;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.UnplannedInput;
import edu.uva.liftlab.graphchecker.contract.ZkChain;
import edu.uva.liftlab.graphchecker.option.LongOptions;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.JsonFields;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * EXPLORE's planner: plan the closure, propose the flips still open, one
 * round at a time.
 *
 * <pre>
 *   --sessions &lt;dir&gt;           the corpus; its parent is the iteration
 *   --target-occurrence &lt;sel&gt;  the case's declared anchor (v1 selector),
 *                              the ONE root of the closure
 *   --static-scope-map &lt;file&gt;  the epoch's write/export sites and guards
 *                              (SYMBOL-SCOPE §3)
 *   --root-domains &lt;file&gt;      what the CASE says each root may be
 *   --topology-epoch &lt;id&gt;      the epoch these sessions belong to
 *   --max-tasks / --max-paths-per-region / --max-flips-per-path /
 *   --max-world-depth
 *   one round, over every session the iteration holds:
 *   --round &lt;n&gt;                which round this is
 *   --results &lt;file&gt;           earlier rounds' ObligationResults; an
 *                              answered query is never proposed again
 *   --in-flight &lt;file&gt;         the obligation rows the campaign has queued
 *                              or running; none is proposed again
 *   --output-dir &lt;dir&gt;         obligations.jsonl, tasks.jsonl, gaps.jsonl,
 *                              graph.jsonl, growth.jsonl, slots.jsonl,
 *                              explore_manifest.json
 *   or every round of the exploration ({@link Service}):
 *   --serve &lt;dir&gt;             answer the rounds asked there, each
 *                              question naming its round, inFlight,
 *                              results (the answers then landed), corpus
 *                              (a file naming the sessions it reads, one
 *                              per line) and outputDir, until the process
 *                              is ended
 * </pre>
 *
 * <p>A round rebuilds the frontier from every session, recorded verdict and
 * arm in flight, writes the unanswered flips, and states the round's wave
 * and the witnesses the corpus holds.  The campaign owns the loop, the
 * workers and every stop (PIPELINE §7.9); it never solves ({@link
 * ObligationSolverMain} does).  ONE planner serves an exploration's rounds:
 * what it read for one round it keeps for the next, so a round reads only
 * the sessions landed since -- the corpus's rows ({@link Corpus#read(Path,
 * Path, Corpus, Collection)}), the static map while its file reads the same,
 * the slot table it folded and changed ({@link SlotTable}) -- and builds
 * every index across sessions anew.  A served round reads the corpus and the
 * answers its question names, frozen by the campaign as the round starts,
 * so the campaign goes on landing, gating and attempting witnesses while it
 * plans (PIPELINE §7.9).  Each round's files are the ones a planner of its
 * own, reading the iteration then, writes (offline-ab.sh EXPLORE.serve).</p>
 */
public final class ExploreMain {
    /** One round's manifest: its anchors, tasks and verdict counts. */
    static final String MANIFEST_FILE = "explore_manifest.json";

    private final Path iteration;
    private final String declaredAnchor;
    private final Path rootDomains;
    private final Path scopeMap;
    private final String topologyEpoch;
    private final int maxTasks;
    private final ObligationFactory.Bounds bounds;
    /** What the last round read, kept for the next. */
    private Corpus corpus;
    private StaticScopeMap scope;
    /** The region plan PLAN froze in the iteration ({@code campaign_plan}):
     *  its rows name the regions each one's occurrences folded. */
    static final String REGION_PLAN = "concolic_region_plan.jsonl";
    private String scopeDigest;
    /** The slot table as the last round left it, and that round. */
    private SlotTable slots;
    private int slotsRound = -1;

    /**
     * One exploration's planner.
     *
     * @param declaredAnchor the case's v1 declaration,
     *                       the closure's only root (PIPELINE §7.1); resolved
     *                       against the seed each round, so nothing
     *                       downstream sees a selector
     */
    ExploreMain(Path iteration, String declaredAnchor, Path rootDomains,
                Path scopeMap, String topologyEpoch, int maxTasks,
                ObligationFactory.Bounds bounds) {
        this.iteration = iteration;
        this.declaredAnchor = declaredAnchor;
        this.rootDomains = rootDomains;
        this.scopeMap = scopeMap;
        this.topologyEpoch = topologyEpoch;
        this.maxTasks = maxTasks;
        this.bounds = bounds;
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
        String declaredAnchor = options.value("target-occurrence", "");
        if (declaredAnchor.isEmpty()) {
            throw new IllegalArgumentException("the closure has no root: "
                    + "pass --target-occurrence. A case declares ONE anchor "
                    + "(PIPELINE §7.1) and the closure is that anchor's");
        }
        // Fail-closed: without the map the closure is the rows' alone, which
        // can miss the writer region the failure depends on (PIPELINE §7.2).
        Path scopeMap = options.path("static-scope-map");
        if (scopeMap == null) {
            throw new IllegalArgumentException("the closure has no static "
                    + "map: pass --static-scope-map. PLAN publishes "
                    + StaticScopeMap.FILE + " per epoch, and the closure "
                    + "needs it to name the writers a replay has not run "
                    + "(PIPELINE §7.2)");
        }
        ExploreMain planner = new ExploreMain(iteration, declaredAnchor,
                options.path("root-domains"), scopeMap,
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
        Path serve = options.path("serve");
        if (serve != null) {
            Service.serve(serve, 0L, (question, out) -> {
                String flying = JsonFields.optionalString(question,
                        "inFlight");
                planner.round(question.get("round").getAsInt(),
                        flying.isEmpty() ? null : Paths.get(flying),
                        Paths.get(JsonFields.primitiveString(question,
                                "results")),
                        corpus(Paths.get(JsonFields.primitiveString(
                                question, "corpus"))),
                        Paths.get(JsonFields.primitiveString(question,
                                "outputDir")));
            });
            return;
        }
        Path out = options.path("output-dir");
        if (out == null) {
            throw new IllegalArgumentException("--serve, or --output-dir, "
                    + "is required");
        }
        System.out.println(pretty(planner.round(
                (int) options.number("round", 0), options.path("in-flight"),
                options.path("results"), null, out)));
    }

    /** The sessions a served round's question names, one per line. */
    private static List<String> corpus(Path file) throws IOException {
        List<String> named = new ArrayList<String>();
        for (String line : Files.readAllLines(file, StandardCharsets.UTF_8)) {
            if (!line.trim().isEmpty()) named.add(line.trim());
        }
        return named;
    }

    /** One round by a planner of its own: {@link #round}. */
    public static JsonObject plan(Path iteration, String declaredAnchor,
                                  Path rootDomains, Path results,
                                  Path inFlight, Path scopeMap, Path out,
                                  int round, String topologyEpoch,
                                  int maxTasks,
                                  ObligationFactory.Bounds bounds)
            throws IOException {
        return new ExploreMain(iteration, declaredAnchor, rootDomains,
                scopeMap, topologyEpoch, maxTasks, bounds)
                .round(round, inFlight, results, null, out);
    }

    /**
     * Plans one round into {@code out}, over the sessions {@code named}
     * names -- null: every session the iteration holds -- and the answers
     * {@code results} holds.
     *
     * @param inFlight the obligation rows queued or running, or null for
     *                 none
     */
    JsonObject round(int round, Path inFlight, Path results,
                     Collection<String> named, Path out) throws IOException {
        corpus = Corpus.read(iteration, rootDomains, corpus, named);
        // The map is read again only when its file changed.
        String digest = Files.isRegularFile(scopeMap)
                ? ArtifactIO.sha256(scopeMap) : "";
        if (scope == null || !digest.equals(scopeDigest)) {
            // With what the plan PLAN froze for this iteration states: the
            // store fetches on a target's data flow
            // (ClosurePlanner#storeFetches).
            scope = StaticScopeMap.read(scopeMap).withPlan(
                    iteration.resolve(REGION_PLAN));
            scopeDigest = digest;
        }
        List<GapRow> gaps = new ArrayList<GapRow>();
        gaps.addAll(unstableAddresses(corpus));
        List<OccurrenceAddress> roots = resolve(corpus, declaredAnchor, gaps);
        Branches branches = Branches.of(corpus, roots, gaps);
        List<Task> tasks = new ArrayList<Task>();
        Map<String, String> why = new LinkedHashMap<String, String>();
        Map<String, Set<String>> flipSites =
                new LinkedHashMap<String, Set<String>>();
        Set<String> opened = new LinkedHashSet<String>();
        Map<OccurrenceAddress, String> grown =
                new LinkedHashMap<OccurrenceAddress, String>();
        Set<OccurrenceAddress> waiting =
                new LinkedHashSet<OccurrenceAddress>();
        List<String> witnesses = witnesses(corpus, roots);
        int truncated = 0;
        int ceilingCut = 0;
        Map<OccurrenceAddress, ClosurePlanner.Concrete> concrete =
                new LinkedHashMap<OccurrenceAddress,
                        ClosurePlanner.Concrete>();
        Set<String> doorsOnly = doorsOnlyOccurrences(iteration);
        Map<OccurrenceAddress, String> unpaused =
                new LinkedHashMap<OccurrenceAddress, String>();
        Set<OccurrenceAddress> runWhole =
                new LinkedHashSet<OccurrenceAddress>();
        for (OccurrenceAddress root : roots) {
            ClosurePlanner.Plan plan = ClosurePlanner.plan(corpus, root,
                    maxTasks, scope, branches, doorsOnly);
            gaps.addAll(plan.gaps);
            if (plan.concrete != null) concrete.put(root, plan.concrete);
            if (!plan.truncated.isEmpty()) {
                // A truncated closure misses arms, but whether that blocks a
                // claim is the exploration's end's to say: none once an
                // accepted witness ended it, else the closure it ended on
                // (the manifest's `truncated`, PIPELINE §7.9).  This round's
                // own is its record.
                truncated += plan.truncated.size();
                ceilingCut += plan.ceilingCut.size();
                gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                        GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        root.render(), "REGION_PATH_CLOSURE_TRUNCATED: closure "
                                + "truncated: static candidates past "
                                + maxTasks + (plan.ceilingCut.isEmpty() ? ""
                                : ", and " + plan.ceilingCut.size()
                                + " occurrence(s) the rows connect past the"
                                + " closure ceiling of "
                                + ClosurePlanner.CLOSURE_CEILING)
                                + "; " + plan.truncated.size()
                                + " occurrences were not planned, so this "
                                + "anchor's closure is incomplete: "
                                + plan.truncated));
            }
            for (Map.Entry<OccurrenceAddress, String> exposure
                    : plan.exposed.entrySet()) {
                grown.putIfAbsent(exposure.getKey(), exposure.getValue());
            }
            waiting.addAll(plan.waiting);
            for (Map.Entry<OccurrenceAddress, String> door
                    : plan.unpaused.entrySet()) {
                unpaused.putIfAbsent(door.getKey(), door.getValue());
            }
            runWhole.addAll(plan.runWhole);
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
        // never empties the round (PIPELINE §7.1).  The table this planner
        // left is the rounds' before this one only when it planned the one
        // before; any other round folds them from their files.
        if (slots == null || slotsRound != round - 1) {
            slots = SlotTable.read(iteration, round);
        }
        slotsRound = -1;
        SlotTable.Reconciliation skeleton = slots.reconcile(corpus, closure,
                round);
        gaps.addAll(skeleton.gaps);

        // The one ledger of owed arms (Frontier).
        Frontier frontier = new Frontier(corpus, tasks, flipSites);
        List<ObligationResult> answers = RowCodec.readAll(results,
                RowCodec::readObligationResult);
        Map<String, List<ObligationResult>> byFlip = answersByFlip(iteration);
        frontier.consume(answers, byFlip);
        if (inFlight != null) {
            frontier.inFlight(RowCodec.readAll(inFlight,
                    ExploreCodec::readObligation));
        }
        List<ObligationFactory.Candidate> candidates =
                new ArrayList<ObligationFactory.Candidate>();
        for (Task task : tasks) {
            candidates.addAll(ObligationFactory.candidates(corpus, task,
                    flipSites.get(task.taskId()), bounds, branches, frontier,
                    gaps));
        }
        // The forced replay of the anchor first (PIPELINE §7.10).
        ForcedFlip.Round forced = ForcedFlip.plan(corpus,
                anchorTask(tasks, roots), scope, frontier, answers, byFlip,
                candidates);
        Frontier.Round open = frontier.open(round, forced.force,
                forced.candidates);

        Files.createDirectories(out);
        // G_k and growth (PIPELINE §7.1); empty growth.jsonl +
        // obligations.jsonl with nothing in flight is the driver's fixed
        // point (§7.9).
        WaveGraph.of(corpus).write(out, round);
        // An address is grown once: a planned occurrence no replay ran again
        // since depends on timing the replays do not reproduce (hdfs-17897
        // v83: the NameNode converts a key command only on the heartbeat that
        // carries one), and growing it again duplicates a plan row.
        Set<String> planned = plannedOccurrences(iteration);
        Set<OccurrenceAddress> unreproduced =
                new LinkedHashSet<OccurrenceAddress>(grown.keySet());
        unreproduced.addAll(waiting);
        for (OccurrenceAddress occurrence : unreproduced) {
            if (!planned.contains(occurrence.render())) continue;
            grown.remove(occurrence);
            waiting.remove(occurrence);
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    occurrence.render(), "planned at this address and no "
                            + "replay since ran it: whether it runs depends "
                            + "on timing the replays do not reproduce, and "
                            + "what it delivered stays in the wire arms"));
        }
        // An invocation is grown once, up to the declared bound: its input
        // already planned (an earlier generation's), or past the bound,
        // named and counted (campaign_bounds).
        Map<UnplannedInput, String> inputs = ClosurePlanner.unplanned(corpus,
                branches);
        Set<String> plannedInputs = plannedInputs(iteration);
        for (Iterator<Map.Entry<UnplannedInput, String>> unplanned
                = inputs.entrySet().iterator(); unplanned.hasNext();) {
            UnplannedInput input = unplanned.next().getKey();
            if (plannedInputs.contains(input.taskId() + " " + input.grown())) {
                unplanned.remove();
            } else if (input.k() > UnplannedInput.MAX) {
                unplanned.remove();
                gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                        GapKind.UNPLANNED_INPUT, GapClass.DIAGNOSTIC,
                        input.subject() + " unplanned-input-max="
                                + UnplannedInput.MAX,
                        "a call of this marker past the "
                                + UnplannedInput.MAX
                                + " invocations of one occurrence GROW plans"
                                + " inputs for: it stays concrete"));
            }
        }
        // The store edges its replays ran past the plan's ZooKeeper chain.
        int exposed = WaveGraph.writeGrowth(corpus, grown, unpaused, inputs,
                ZkEdges.of(corpus, ZkChain.read(
                        iteration.resolve(ZkChain.FILE))), out);
        // What only the seed replay ran waits for a focused replay to expose
        // it -- unless this round is the fixpoint: then none ever will, and
        // the closure is incomplete.
        boolean fixpoint = open.empty() && exposed == 0
                && frontier.inFlightCount() == 0 && witnesses.isEmpty();
        // A doors-only occurrence demanded as a value that no replay ran
        // whole, and none GROW can re-run (the seed is not): at the fixed
        // point no replay ever will.
        if (fixpoint) {
            for (OccurrenceAddress paused : runWhole) {
                gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                        GapKind.ADMISSION_GAP, GapClass.BLOCKING,
                        paused.render(), "demanded as a value and run for"
                                + " its doors alone by every session that"
                                + " captured it, and the exploration ends"
                                + " here: no replay ran it whole, so its"
                                + " guards and roots were never flippable"));
            }
        }
        for (OccurrenceAddress unexposed : waiting) {
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, fixpoint ? GapClass.BLOCKING
                            : GapClass.DIAGNOSTIC, unexposed.render(),
                    "only the seed replay ran this occurrence, under no "
                            + "planned task, and "
                            + (fixpoint ? "the exploration ends here: no "
                            + "focused replay ran it, so it is never a task"
                            : "the first admitted focused replay that runs "
                            + "it exposes it")));
        }
        RowCodec.writeAll(out.resolve("tasks.jsonl"), tasks,
                ExploreCodec::writeTask);
        // An empty file IS the frontier closing.
        RowCodec.writeAll(out.resolve("obligations.jsonl"), open.obligations,
                ExploreCodec::writeObligation);
        // A cycle past the naming budget keys its arms by reference: named.
        String namingCut = corpus.namingCut();
        if (namingCut != null) {
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC, "arm keys",
                    namingCut));
        }
        RowCodec.writeAll(out.resolve("gaps.jsonl"), distinct(gaps),
                RowCodec::writeGap);
        JsonObject manifest = manifest(roots, tasks, why, frontier, open,
                topologyEpoch, gaps, slots, skeleton, exposed, truncated,
                ceilingCut, witnesses, wave(iteration, corpus), branches,
                concrete);
        manifest.add("openArms", openArms(corpus, roots, tasks, frontier,
                open, byFlip));
        manifest.add("boundedFlips", boundedFlips(iteration,
                frontier.boundedFlips()));
        manifest.add("force", forced.manifest);
        Files.write(out.resolve(MANIFEST_FILE),
                (pretty(manifest) + System.lineSeparator())
                        .getBytes(StandardCharsets.UTF_8));
        // Last: the round's change of the slot table, so a round planned
        // again starts from the table the rounds before it left.
        slots.write(out);
        slotsRound = round;
        return manifest;
    }

    /** The declared anchor's task among a round's, or null. */
    private static Task anchorTask(List<Task> tasks,
                                   List<OccurrenceAddress> roots) {
        for (Task task : tasks) {
            if (roots.contains(task.focused())) return task;
        }
        return null;
    }

    /**
     * The open decider arms the declared anchor's reached, admitted runs left
     * phi without (TargetRow.OpenArm, causynth.BooleanReturns) and no run
     * took, each with what its flip came to on the paths that left it: a
     * path's flip TAKEN where a replay ran it ({@code ADMITTED}) or another
     * recorded path took it -- phi states the arm there, and an arm one path
     * took is not listed -- {@code UNSAT} where no world of the corpus takes
     * it, {@code PENDING} while one is in flight or proposed (a flip asked
     * again without a world its replay refuted among them), {@code
     * UNANSWERED} where its flip came to anything else (a replay that never
     * reached the decision and refuted nothing, NOT_ADMITTED), {@code
     * NOT_ASKED} where no round cut it from that path, {@code NOT_FLIPPABLE}
     * where no decision under it states a predicate.  The arm's state is the
     * first of UNANSWERED, NOT_ASKED, PENDING, NOT_FLIPPABLE, UNSAT any of
     * its paths is in.  Each world a replay of its flip refuted
     * (WORLD_REFUTED, {@link Corpus#refutedWorlds}) is named on the row
     * ({@code refutedWorlds}: its digest, obligation, session, the
     * conditions that held, the workload's terminating exception and where
     * it was thrown): an UNSAT rests on them.  EMIT names each arm
     * (result.json concrete[] OPEN_ARM): an UNSAT closes over none but an
     * UNSAT one, and an UNANSWERED one leaves no verdict.
     */
    static JsonArray openArms(Corpus corpus, List<OccurrenceAddress> roots,
                              List<Task> tasks, Frontier frontier,
                              Frontier.Round open,
                              Map<String, List<ObligationResult>> answers) {
        // Each proposed obligation by its id and by its flip.
        Set<String> proposed = new LinkedHashSet<String>();
        for (Obligation obligation : open.obligations) {
            proposed.add(obligation.obligationId());
            proposed.add(ObligationFactory.flip(obligation.taskId(),
                    obligation.pathId(), obligation.siteId(),
                    obligation.ordinal(), obligation.flippedOutcome()));
        }
        String[] order = {"UNANSWERED", "NOT_ASKED", "PENDING",
                "NOT_FLIPPABLE", BOUNDED, "UNSAT"};
        JsonArray arms = new JsonArray();
        for (OccurrenceAddress root : roots) {
            Task task = null;
            for (Task candidate : tasks) {
                if (candidate.focused().equals(root)) task = candidate;
            }
            Map<String, Map<String, Integer>> states =
                    new LinkedHashMap<String, Map<String, Integer>>();
            Map<String, Set<String>> asked =
                    new LinkedHashMap<String, Set<String>>();
            Map<String, Map<String, JsonObject>> refuted =
                    new LinkedHashMap<String, Map<String, JsonObject>>();
            Map<String, Set<String>> unrun =
                    new LinkedHashMap<String, Set<String>>();
            Map<String, Set<String>> refusals =
                    new LinkedHashMap<String, Set<String>>();
            Set<String> taken = new LinkedHashSet<String>();
            for (TargetRow row : corpus.targetsOn(root)) {
                TargetRow.OpenArm arm = row.openArm();
                SessionReader session = corpus.session(row.sessionId());
                if (arm == null || !row.reachedAnchor() || session == null
                        || !session.admitted()) {
                    continue;
                }
                String key = arm.siteId() + "=" + arm.outcome();
                Map<String, JsonObject> worlds = refuted.computeIfAbsent(key,
                        k -> new LinkedHashMap<String, JsonObject>());
                String state = openArmState(corpus, task, root, row, arm,
                        frontier, proposed, answers, worlds,
                        unrun.computeIfAbsent(key,
                                k -> new LinkedHashSet<String>()),
                        refusals.computeIfAbsent(key,
                                k -> new LinkedHashSet<String>()));
                if ("TAKEN".equals(state)) taken.add(key);
                states.computeIfAbsent(key,
                        k -> new LinkedHashMap<String, Integer>())
                        .merge(state, 1, Integer::sum);
                if (!arm.askedSiteId().isEmpty()) {
                    asked.computeIfAbsent(key,
                            k -> new LinkedHashSet<String>())
                            .add(FlipQuery.asked(arm.askedSiteId(),
                                    arm.askedOrdinal()));
                }
            }
            for (Map.Entry<String, Map<String, Integer>> arm
                    : states.entrySet()) {
                if (taken.contains(arm.getKey())) continue;
                String state = "";
                for (String candidate : order) {
                    if (arm.getValue().containsKey(candidate)) {
                        state = candidate;
                        break;
                    }
                }
                int split = arm.getKey().lastIndexOf('=');
                JsonObject row = new JsonObject();
                row.addProperty("anchor", root.render());
                row.addProperty("siteId", arm.getKey().substring(0, split));
                row.addProperty("outcome", Boolean.parseBoolean(
                        arm.getKey().substring(split + 1)));
                row.addProperty("state", state);
                JsonObject paths = new JsonObject();
                for (Map.Entry<String, Integer> count
                        : arm.getValue().entrySet()) {
                    paths.addProperty(count.getKey(), count.getValue());
                }
                row.add("paths", paths);
                row.add("asked", ExploreCodec.list(new ArrayList<String>(
                        asked.getOrDefault(arm.getKey(),
                                new LinkedHashSet<String>()))));
                JsonArray worlds = new JsonArray();
                for (JsonObject world : refuted.get(arm.getKey()).values()) {
                    worlds.add(world);
                }
                row.add("refutedWorlds", worlds);
                row.add("unrunWorlds", ExploreCodec.list(new ArrayList<String>(
                        unrun.get(arm.getKey()))));
                // The arm's query refused at the arm: named, never closed.
                row.add("refused", ExploreCodec.list(new ArrayList<String>(
                        refusals.get(arm.getKey()))));
                arms.add(row);
            }
        }
        return arms;
    }

    /** An open arm whose flip is asked no more past {@link
     *  ObligationFactory#MAX_REFUTED_WORLDS} refuted worlds: the named
     *  valve, result.json {@code bounded}. */
    static final String BOUNDED = "BOUNDED";

    /**
     * What one path's flip of its open arm came to ({@link #openArms}).  Its
     * own FLIP -- task, path, decision, outcome, the key {@link
     * Corpus#refutedWorlds} uses -- decides where it was asked: every answer
     * that flip got, in wave order, whatever id each ran under, since the id
     * moves as the corpus grows and one flip's answers land under several
     * (hdfs-adhoc-39 WD2: the re-ask of a refuted flip came UNSAT under
     * another id).  A path that never asked its own flip shares the answer
     * of the arm its id names, as the id is meant to (Frontier: an arm is
     * owed once per dependence, not per path), and so does one whose only
     * answers refuted worlds (a refutation answers nothing of the arm; the
     * shared id's UNSAT may settle it before its own re-ask: hdfs-adhoc-39
     * OK1-0).  TAKEN where any answer admitted it or a recorded path took
     * it; else what its last answer says.  The worlds its replays refuted
     * are added to {@code
     * refuted}, by digest; each replay that did not run its world ({@code
     * ObligationResult#worldUnrefuted}: asked once more, {@link
     * Frontier#consume}) to {@code unrun}, as obligation@session; each
     * refusal at the arm ({@code ObligationResult#ARM_REFUSED}), its own
     * flip's or its id's, to {@code refusals}: the arm stays open, by name.
     */
    private static String openArmState(Corpus corpus, Task task,
                                       OccurrenceAddress root, TargetRow row,
                                       TargetRow.OpenArm arm,
                                       Frontier frontier,
                                       Set<String> proposed,
                                       Map<String, List<ObligationResult>>
                                               answers,
                                       Map<String, JsonObject> refuted,
                                       Set<String> unrun,
                                       Set<String> refusals) {
        if (arm.askedSiteId().isEmpty()) return "NOT_FLIPPABLE";
        if (task == null) return "NOT_ASKED";
        for (Corpus.RecordedPath path : corpus.pathsOf(root)) {
            if (!path.sessionId.equals(row.sessionId())) continue;
            for (int index = 0; index < path.decisions.size(); index++) {
                DecisionRow decision = path.decisions.get(index);
                if (!decision.siteId().equals(arm.askedSiteId())
                        || decision.ordinal() != arm.askedOrdinal()) {
                    continue;
                }
                String flip = ObligationFactory.flip(task.taskId(),
                        path.pathId, decision.siteId(), decision.ordinal(),
                        !decision.outcome());
                List<Corpus.Refuted> worlds = corpus.refutedWorlds(flip);
                for (Corpus.Refuted world : worlds) {
                    refuted.putIfAbsent(world.digest, refutedWorld(world));
                }
                String id = ObligationFactory.obligationId(task.taskId(),
                        decision.siteId(), decision.ordinal(),
                        !decision.outcome(), ObligationFactory.dependence(
                                corpus, task, path, index));
                Verdict shared = frontier.verdict(id);
                if (frontier.recorded(id) || shared == Verdict.ADMITTED) {
                    return "TAKEN";
                }
                Verdict last = null;
                String atArm = frontier.armRefusal(id);
                if (atArm != null) refusals.add(atArm);
                for (ObligationResult answer : answers.getOrDefault(flip,
                        Collections.<ObligationResult>emptyList())) {
                    if (answer.verdict() == Verdict.ADMITTED) return "TAKEN";
                    if (answer.armRefusal() != null) {
                        refusals.add(answer.armRefusal());
                    }
                    if (answer.worldUnrefuted()) {
                        unrun.add(answer.obligationId() + "@"
                                + answer.sessionId());
                    }
                    // A refuted world answers nothing of the arm (Frontier
                    // #consume): only its re-ask, or the shared id's, does.
                    if (answer.verdict() != Verdict.SAT_MODEL_READY
                            && answer.refutation() == null) {
                        last = answer.verdict();
                    }
                }
                if (last == null) last = shared;
                if (last == Verdict.UNSAT) return "UNSAT";
                if (frontier.flying(flip) || proposed.contains(flip)
                        || frontier.inFlight(id) || proposed.contains(id)) {
                    return "PENDING";
                }
                if (Corpus.distinctWorlds(worlds)
                        >= ObligationFactory.MAX_REFUTED_WORLDS) {
                    return BOUNDED;
                }
                return last != null ? "UNANSWERED" : "NOT_ASKED";
            }
        }
        return "NOT_ASKED";
    }

    /**
     * Every answer this iteration's obligation workers wrote, by the flip
     * each asked ({@link ObligationFactory#flip}), in wave and name order:
     * its question names the flip ({@code <flip>:<content>},
     * {@link ObligationFactory#question}), else its ask's row does.
     */
    static Map<String, List<ObligationResult>> answersByFlip(Path iteration)
            throws IOException {
        Map<String, List<ObligationResult>> byFlip =
                new LinkedHashMap<String, List<ObligationResult>>();
        for (Path worker : ObligationDir.workerDirs(iteration)) {
            List<ObligationResult> results = RowCodec.readAll(
                    worker.resolve(ObligationDir.RESULT),
                    RowCodec::readObligationResult);
            String flip = results.isEmpty() ? "" : flipOf(worker);
            if (flip.isEmpty()) continue;
            byFlip.computeIfAbsent(flip,
                    key -> new ArrayList<ObligationResult>()).addAll(results);
        }
        return byFlip;
    }

    /**
     * The flips held BOUNDED by {@code replay_timeout_s} ({@link
     * Frontier#boundedFlips}), each by the arm its workers asked (task,
     * path, site, ordinal, the outcome asked; {@code force} for the FORCE
     * run, which asks none, {@link ForcedFlip#flip}) and the obligations whose
     * replays were killed with what killed them: what run_engine's {@code
     * campaign_bounds} names, the last round's being every one.
     */
    static JsonArray boundedFlips(Path iteration, Set<String> flips)
            throws IOException {
        Map<String, JsonObject> rows = new LinkedHashMap<String, JsonObject>();
        if (flips.isEmpty()) return new JsonArray();
        for (Path worker : ObligationDir.workerDirs(iteration)) {
            List<ObligationResult> results = RowCodec.readAll(
                    worker.resolve(ObligationDir.RESULT),
                    RowCodec::readObligationResult);
            if (results.isEmpty()) continue;
            String flip = flipOf(worker);
            if (!flips.contains(flip)) continue;
            List<Obligation> asked = RowCodec.readAll(
                    worker.resolve(ObligationDir.OBLIGATION),
                    ExploreCodec::readObligation);
            JsonObject row = rows.get(flip);
            if (row == null && !asked.isEmpty()) {
                Obligation ask = asked.get(0);
                row = new JsonObject();
                row.addProperty("flip", flip);
                row.addProperty("taskId", ask.taskId());
                row.addProperty("pathId", ask.pathId());
                row.addProperty("siteId", ask.siteId());
                row.addProperty("ordinal", ask.ordinal());
                row.addProperty("outcome", ask.flippedOutcome());
                // The FORCE run, which flips nothing (ForcedFlip#flip).
                if (ask.force()) row.addProperty("force", true);
                row.add("killed", new JsonArray());
                rows.put(flip, row);
            }
            if (row == null) continue;
            for (ObligationResult result : results) {
                if (!result.replayBounded()) continue;
                JsonObject killed = new JsonObject();
                killed.addProperty("obligationId", result.obligationId());
                killed.addProperty("detail", result.detail());
                row.getAsJsonArray("killed").add(killed);
            }
        }
        JsonArray out = new JsonArray();
        for (JsonObject row : rows.values()) out.add(row);
        return out;
    }

    /** The flip one worker's obligation asked, or "" where it states
     *  none. */
    private static String flipOf(Path worker) throws IOException {
        for (String file : new String[] {ObligationDir.QUESTION,
                ObligationDir.QUESTION_ASKED}) {
            Path question = worker.resolve(file);
            if (!Files.isRegularFile(question)) continue;
            String text = new String(Files.readAllBytes(question),
                    StandardCharsets.UTF_8).trim();
            int colon = text.indexOf(':');
            if (colon > 0) return text.substring(0, colon);
        }
        List<Obligation> asked = RowCodec.readAll(
                worker.resolve(ObligationDir.OBLIGATION),
                ExploreCodec::readObligation);
        if (asked.isEmpty()) return "";
        Obligation ask = asked.get(0);
        return ObligationFactory.flip(ask.taskId(), ask.pathId(),
                ask.siteId(), ask.ordinal(), ask.flippedOutcome());
    }

    /** One refuted world as an open arm's row names it. */
    private static JsonObject refutedWorld(Corpus.Refuted world) {
        JsonObject row = new JsonObject();
        row.addProperty("world", world.digest);
        row.addProperty("obligationId", world.obligationId);
        row.addProperty("sessionId", world.sessionId);
        JsonObject why = RowCodec.writeRefutation(world.refutation);
        for (Map.Entry<String, JsonElement> member : why.entrySet()) {
            row.add(member.getKey(), member.getValue());
        }
        return row;
    }

    /**
     * A CONCRETE ANCHOR (R1-ROOTS D0): every admitted path decided it on no
     * symbol, so its decision is a constant of the formula (COMPOSE states
     * its healthy arm as one) and its closure starts from what it read on its
     * path guards' cone before it decided ({@link ClosurePlanner.Concrete}).
     * Information, never a gap: what the decision rested on concretely --
     * its paths, how many decided it on the way to the throw, the reads its
     * closure demands and their locations, and how many earlier reads off
     * the cone the root demand left out (root_demand.jsonl).
     */
    private static JsonObject concreteRow(OccurrenceAddress anchor,
                                          ClosurePlanner.Concrete concrete) {
        Set<String> locations = new TreeSet<String>();
        for (ReadRow read : concrete.reads) {
            locations.add(SmtLowering.locationKey(read.location()));
        }
        JsonObject row = new JsonObject();
        row.addProperty("anchor", anchor.render());
        row.addProperty("paths", concrete.paths);
        row.addProperty("decided", concrete.decided);
        row.addProperty("reads", concrete.reads.size());
        row.add("locations", ExploreCodec.list(
                new ArrayList<String>(locations)));
        row.addProperty("offCone", concrete.offCone);
        return row;
    }

    /**
     * THE WITNESSES: every admitted focused replay (in reading order) whose
     * target row at a declared root observed the fatal.  The question is
     * that one (r,c,i) occurrence, so what a run did after its fatal is not
     * the bug's (owner 2026-09-28: hdfs-11741, hdfs-17899-bug2 kept
     * exploring for waves after it).  The campaign tries to end at each one
     * as it lands, by the same rule over the manifest's anchorOccurrences
     * (PIPELINE §7.9); here they class the closure's gaps.
     */
    private static List<String> witnesses(Corpus corpus,
                                          List<OccurrenceAddress> roots) {
        Set<String> witnessed = new LinkedHashSet<String>();
        for (OccurrenceAddress root : roots) {
            for (TargetRow row : corpus.targetsOn(root)) {
                SessionReader session = corpus.session(row.sessionId());
                if (row.observedFatal() && session != null
                        && !session.seed() && session.admitted()) {
                    witnessed.add(row.sessionId());
                }
            }
        }
        return new ArrayList<String>(witnessed);
    }

    /**
     * THE WAVE this round plans, a generation of worlds: one past the
     * deepest wave whose obligation published a session of this corpus, 0
     * over the seed alone (a round's wave is its manifest's; one that states
     * none planned from the seed).  It deepens only as sessions land, never
     * with the rounds a streaming campaign plans between them, and
     * {@code region_path_max_waves} bounds it (PIPELINE §7.9).
     */
    private static int wave(Path iteration, Corpus corpus)
            throws IOException {
        Map<Path, Integer> waves = new LinkedHashMap<Path, Integer>();
        int deepest = 0;
        for (ObligationDir worker : ObligationDir.workersIn(iteration)) {
            if (corpus.session(worker.sessionId()) == null) continue;
            Path round = worker.dir().getParent();
            Integer of = waves.get(round);
            if (of == null) {
                Path manifest = round.resolve(MANIFEST_FILE);
                JsonObject stated = Files.isRegularFile(manifest)
                        ? ExploreCodec.readObject(manifest) : null;
                of = stated != null && stated.has("wave")
                        ? stated.get("wave").getAsInt() : 0;
                waves.put(round, of);
            }
            deepest = Math.max(deepest, of + 1);
        }
        return deepest;
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
     * Resolves the declared anchor via {@link SelectorResolution} (IDENTITY
     * §9) and refuses the round, BLOCKING, when it does not resolve -- naming
     * what the seed ran that region as, since the cause is usually a spelling
     * mismatch. A full address resolves by parsing alone, so it is also checked
     * against the seed's activations: no replay can focus an occurrence no run
     * recorded (PIPELINE §7.1). The closure is the ANCHOR's only; plan rows
     * are not roots.
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

    /** The occurrence address of every task row the iteration's plan holds,
     *  grown rows included. */
    private static Set<String> plannedOccurrences(Path iteration)
            throws IOException {
        Set<String> planned = new LinkedHashSet<String>();
        Path plan = iteration.resolve("execution_task_plan.jsonl");
        if (!Files.exists(plan)) return planned;
        for (JsonObject row : RowCodec.readJsonl(plan)) {
            if (row.has("occurrenceId")) {
                planned.add(row.get("occurrenceId").getAsString());
            }
        }
        return planned;
    }

    /** {@code <taskId> <symbol>} of every input the iteration's plan holds,
     *  grown inputs included. */
    private static Set<String> plannedInputs(Path iteration)
            throws IOException {
        Set<String> planned = new LinkedHashSet<String>();
        Path plan = iteration.resolve("execution_task_plan.jsonl");
        if (!Files.exists(plan)) return planned;
        for (JsonObject row : RowCodec.readJsonl(plan)) {
            if (!row.has(InputActionCatalog.FIELD)) continue;
            String taskId = row.has("taskId")
                    ? row.get("taskId").getAsString() : "";
            for (JsonElement action
                    : row.getAsJsonArray(InputActionCatalog.FIELD)) {
                JsonObject input = action.getAsJsonObject();
                if (input.has("symbol")) {
                    planned.add(taskId + " "
                            + input.get("symbol").getAsString());
                }
            }
        }
        return planned;
    }

    /** The occurrences the current plan runs for their doors alone
     *  ({@code RuntimeSelectedRegionFinalizer#DOORS_ONLY} on their task row;
     *  GROW drops it from one a value demand reaches). */
    private static Set<String> doorsOnlyOccurrences(Path iteration)
            throws IOException {
        Set<String> doorsOnly = new LinkedHashSet<String>();
        Path plan = iteration.resolve("execution_task_plan.jsonl");
        if (!Files.exists(plan)) return doorsOnly;
        for (JsonObject row : RowCodec.readJsonl(plan)) {
            if (row.has(RuntimeSelectedRegionFinalizer.DOORS_ONLY)
                    && row.get(RuntimeSelectedRegionFinalizer.DOORS_ONLY)
                    .getAsBoolean() && row.has("occurrenceId")) {
                doorsOnly.add(row.get("occurrenceId").getAsString());
            }
        }
        return doorsOnly;
    }

    /** Every occurrence this round's tasks hold: focused, and their factors. */
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
                                       Frontier.Round open,
                                       String topologyEpoch,
                                       List<GapRow> gaps, SlotTable slots,
                                       SlotTable.Reconciliation skeleton,
                                       int exposed, int truncated,
                                       int ceilingCut,
                                       List<String> witnesses,
                                       int wave, Branches branches,
                                       Map<OccurrenceAddress,
                                               ClosurePlanner.Concrete>
                                               concrete) {
        JsonObject manifest = new JsonObject();
        JsonArray anchors = new JsonArray();
        // The same anchors as a target row spells its occurrence, so the
        // campaign tells a landed session's witness by equality alone.
        JsonArray anchorOccurrences = new JsonArray();
        for (OccurrenceAddress root : roots) {
            anchors.add(root.render());
            anchorOccurrences.add(RowCodec.writeOccurrence(root));
        }
        manifest.add("anchors", anchors);
        manifest.add("anchorOccurrences", anchorOccurrences);
        manifest.addProperty("topologyEpoch", topologyEpoch);
        manifest.addProperty("round", open.index);
        manifest.addProperty("wave", wave);
        // FIXED_POINT: nothing proposed, exposed or in flight; AWAITING:
        // nothing new while arms are still in flight.
        manifest.addProperty("state", !open.empty() || exposed > 0
                ? "OBLIGATIONS_PROPOSED" : frontier.inFlightCount() > 0
                ? "AWAITING" : "FIXED_POINT");
        manifest.add("witnesses", ExploreCodec.list(witnesses));
        manifest.addProperty("inFlight", frontier.inFlightCount());
        manifest.addProperty("heldInFlight", open.heldInFlight);
        manifest.addProperty("branchesStopped", branches.stopped());
        manifest.addProperty("exposedRegions", exposed);
        // Occurrences this round's closure did not plan: static candidates
        // past --max-tasks, and of them those the rows connect past the
        // closure ceiling (ClosurePlanner#CLOSURE_CEILING).
        manifest.addProperty("truncated", truncated);
        manifest.addProperty("ceilingCut", ceilingCut);
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
        JsonArray concreteAnchors = new JsonArray();
        for (Map.Entry<OccurrenceAddress, ClosurePlanner.Concrete> anchor
                : concrete.entrySet()) {
            concreteAnchors.add(concreteRow(anchor.getKey(),
                    anchor.getValue()));
        }
        manifest.add("concreteAnchors", concreteAnchors);
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
