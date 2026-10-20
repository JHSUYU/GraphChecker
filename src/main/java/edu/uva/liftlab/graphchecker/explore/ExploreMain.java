package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.contract.HeapWatch;
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
import edu.uva.liftlab.graphchecker.contract.Parallel;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.plan.SelectorResolution;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.plan.SystemView;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
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

public final class ExploreMain {
    static final String MANIFEST_FILE = "explore_manifest.json";
    static final String TASKS_FILE = "tasks.jsonl.gz";
    public static final String GAPS_FILE = "gaps.jsonl.gz";
    static final String CORPUS_READ = "corpus_read";

    private final Path iteration;
    private final String declaredAnchor;
    private final Path rootDomains;
    private final Path scopeMap;
    private final String topologyEpoch;
    private final int maxTasks;
    private final ObligationFactory.Bounds bounds;
    private final ClientFaults faults;
    private final SystemView view;
    private Corpus corpus;
    private StaticScopeMap scope;
    static final String REGION_PLAN = "concolic_region_plan.jsonl";
    private String scopeDigest;
    private SlotTable slots;
    private int slotsRound = -1;
    private final List<Parallel.Beside> writing =
            new ArrayList<Parallel.Beside>();

    ExploreMain(Path iteration, String declaredAnchor, Path rootDomains,
                Path scopeMap, String topologyEpoch, int maxTasks,
                ObligationFactory.Bounds bounds, ClientFaults faults,
                SystemView view) {
        this.iteration = iteration;
        this.declaredAnchor = declaredAnchor;
        this.rootDomains = rootDomains;
        this.scopeMap = scopeMap;
        this.topologyEpoch = topologyEpoch;
        this.maxTasks = maxTasks;
        this.bounds = bounds;
        this.faults = faults;
        this.view = view;
    }

    public static void main(String[] argv) throws Exception {
        HeapWatch.start();
        Parallel.width(Parallel.HOST_CORES);
        LongOptions options = LongOptions.parse(argv);
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
                                ObligationFactory.DEFAULT_MAX_WORLD_DEPTH)),
                ClientFaults.read(options.path("system-doors"),
                        transports(options.value("client-fault-transports",
                                ""))),
                SystemView.of(options.value("system-view", "")));
        Path serve = options.path("serve");
        if (serve != null) {
            Service.serve(serve, 0L, 1, (question, out) -> {
                String flying = JsonFields.optionalString(question,
                        "inFlight");
                List<String> named = corpus(Paths.get(
                        JsonFields.primitiveString(question, "corpus")));
                long[] live = HeapWatch.takePeakSwept();
                long toRead = planner.toRead(named);
                System.err.printf("round %d: the planner's live set %d MB at "
                                + "its highest of its %d MB old generation, "
                                + "%d MB of session files to read%n",
                        question.get("round").getAsInt(), live[0] >> 20,
                        live[1] >> 20, toRead >> 20);
                String past = HeapWatch.outgrown("the planner", live[0],
                        live[1], toRead);
                if (past != null) throw new Service.OutOfHeap(past);
                Path planned = Paths.get(JsonFields.primitiveString(question,
                        "outputDir"));
                planner.round(question.get("round").getAsInt(),
                        flying.isEmpty() ? null : Paths.get(flying),
                        Paths.get(JsonFields.primitiveString(question,
                                "results")), named, planned);
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

    long toRead(Collection<String> named) throws IOException {
        Set<String> held = new LinkedHashSet<String>();
        if (corpus != null) {
            for (SessionReader session : corpus.everySession()) {
                held.add(session.sessionId());
            }
        }
        long bytes = 0L;
        for (String sessionId : named) {
            if (held.contains(sessionId)) continue;
            try (java.nio.file.DirectoryStream<Path> files = Files
                    .newDirectoryStream(SessionDir.of(iteration, sessionId)
                            .dir())) {
                for (Path file : files) bytes += ArtifactIO.decodedSize(file);
            }
        }
        return bytes;
    }

    private static List<String> corpus(Path file) throws IOException {
        List<String> named = new ArrayList<String>();
        for (String line : Files.readAllLines(file, StandardCharsets.UTF_8)) {
            if (!line.trim().isEmpty()) named.add(line.trim());
        }
        return named;
    }

    public static JsonObject plan(Path iteration, String declaredAnchor,
                                  Path rootDomains, Path results,
                                  Path inFlight, Path scopeMap, Path out,
                                  int round, String topologyEpoch,
                                  int maxTasks,
                                  ObligationFactory.Bounds bounds)
            throws IOException {
        return new ExploreMain(iteration, declaredAnchor, rootDomains,
                scopeMap, topologyEpoch, maxTasks, bounds, ClientFaults.NONE,
                SystemView.of(""))
                .round(round, inFlight, results, null, out);
    }

    private static List<String> transports(String value) {
        List<String> names = new ArrayList<String>();
        for (String name : value.split(",")) {
            if (!name.trim().isEmpty()) names.add(name.trim());
        }
        return names;
    }

    JsonObject round(int round, Path inFlight, Path results,
                     Collection<String> named, Path out) throws IOException {
        try (RoundGaps gaps = new RoundGaps(out.resolve(GAPS_FILE))) {
            return round(round, inFlight, results, named, out, gaps);
        }
    }

    private JsonObject round(int round, Path inFlight, Path results,
                             Collection<String> named, Path out,
                             RoundGaps gaps) throws IOException {
        for (Parallel.Beside file : writing) file.await();
        writing.clear();
        corpus = Corpus.read(iteration, rootDomains, corpus, named);
        Files.createDirectories(out);
        Files.write(out.resolve(CORPUS_READ), new byte[0]);
        String digest = Files.isRegularFile(scopeMap)
                ? ArtifactIO.sha256(scopeMap) : "";
        if (scope == null || !digest.equals(scopeDigest)) {
            scope = StaticScopeMap.read(scopeMap).withPlan(
                    iteration.resolve(REGION_PLAN));
            scopeDigest = digest;
        }
        List<GapRow> said = unstableAddresses(corpus);
        List<OccurrenceAddress> roots = resolve(corpus, declaredAnchor, said);
        Branches branches = Branches.of(corpus, roots, said);
        gaps.addAll(said);
        List<Task> tasks = new ArrayList<Task>();
        Map<String, String> why = new LinkedHashMap<String, String>();
        Map<String, Set<String>> flipSites =
                new LinkedHashMap<String, Set<String>>();
        Set<String> opened = new LinkedHashSet<String>();
        Map<OccurrenceAddress, String> grown =
                new LinkedHashMap<OccurrenceAddress, String>();
        Set<OccurrenceAddress> waiting =
                new LinkedHashSet<OccurrenceAddress>();
        Map<String, Set<OccurrenceAddress>> unrecorded =
                new LinkedHashMap<String, Set<OccurrenceAddress>>();
        List<String> witnesses = witnesses(corpus, roots);
        int truncated = 0;
        int ceilingCut = 0;
        Map<OccurrenceAddress, ClosurePlanner.Concrete> concrete =
                new LinkedHashMap<OccurrenceAddress,
                        ClosurePlanner.Concrete>();
        Set<String> doorsOnly = doorsOnlyOccurrences(iteration,
                RuntimeSelectedRegionFinalizer.DOORS_ONLY);
        Set<String> heldDoorsOnly = doorsOnlyOccurrences(iteration,
                RuntimeSelectedRegionFinalizer.DOORS_ONLY_DECLARED);
        Map<OccurrenceAddress, String> unpaused =
                new LinkedHashMap<OccurrenceAddress, String>();
        Set<OccurrenceAddress> runWhole =
                new LinkedHashSet<OccurrenceAddress>();
        for (OccurrenceAddress root : roots) {
            ClosurePlanner.Plan plan = ClosurePlanner.plan(corpus, root,
                    maxTasks, scope, branches, doorsOnly, heldDoorsOnly,
                    faults, view, gaps);
            if (plan.concrete != null) concrete.put(root, plan.concrete);
            if (!plan.truncated.isEmpty()) {
                truncated += plan.truncated.size();
                ceilingCut += plan.ceilingCut.size();
                gaps.accept(GapRow.of(ExploreCodec.EXPLORATION,
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
            for (Map.Entry<String, Set<OccurrenceAddress>> read
                    : plan.unrecordedWriters.entrySet()) {
                unrecorded.computeIfAbsent(read.getKey(),
                        key -> new LinkedHashSet<OccurrenceAddress>())
                        .addAll(read.getValue());
            }
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
        if (slots == null || slotsRound != round - 1) {
            slots = SlotTable.read(iteration, round);
        }
        slotsRound = -1;
        JsonObject skeleton = skeleton(slots, slots.reconcile(corpus, closure,
                round), gaps);
        SlotTable changed = slots;
        writing.add(Parallel.beside("slots", () -> changed.write(out)));

        Frontier frontier = new Frontier(corpus, tasks, flipSites);
        List<ObligationResult> answers = RowCodec.readAll(results,
                RowCodec::readObligationResult);
        Map<String, List<ObligationResult>> byFlip = answersByFlip(iteration);
        frontier.consume(answers, byFlip);
        if (inFlight != null) {
            frontier.inFlight(RowCodec.readAll(inFlight,
                    ExploreCodec::readObligation));
        }
        ZkChain chain = ZkChain.read(iteration.resolve(ZkChain.FILE));
        ZkKeys keys = ZkKeys.of(chain);
        List<GapRow> offering = new ArrayList<GapRow>();
        List<ObligationFactory.Candidate> candidates =
                ObligationFactory.candidates(corpus, tasks, flipSites, bounds,
                        branches, frontier, offering, keys);
        gaps.addAll(offering);
        ForcedFlip.Round forced = ForcedFlip.plan(corpus,
                anchorTask(tasks, roots), scope, frontier, answers, byFlip,
                candidates);
        Set<String> planned = plannedOccurrences(iteration);
        List<Obligation> first = new ArrayList<Obligation>();
        if (forced.force != null) first.add(forced.force);
        first.addAll(PathReruns.of(corpus, anchorTask(tasks, roots),
                unrecorded, planned, frontier, byFlip, gaps::accept));
        Frontier.Round open = frontier.open(round, first, forced.candidates);

        Files.createDirectories(out);
        WaveGraph graph = WaveGraph.of(corpus);
        writing.add(Parallel.beside("graph", () -> graph.write(out, round)));
        Set<OccurrenceAddress> unreproduced =
                new LinkedHashSet<OccurrenceAddress>(grown.keySet());
        unreproduced.addAll(waiting);
        for (OccurrenceAddress occurrence : unreproduced) {
            if (!planned.contains(occurrence.render())) continue;
            grown.remove(occurrence);
            waiting.remove(occurrence);
            gaps.accept(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    occurrence.render(), "planned at this address and no "
                            + "replay since ran it: whether it runs depends "
                            + "on timing the replays do not reproduce, and "
                            + "what it delivered stays in the wire arms"));
        }
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
                gaps.accept(GapRow.of(ExploreCodec.EXPLORATION,
                        GapKind.UNPLANNED_INPUT, GapClass.DIAGNOSTIC,
                        input.subject() + " unplanned-input-max="
                                + UnplannedInput.MAX,
                        "a call of this marker past the "
                                + UnplannedInput.MAX
                                + " invocations of one occurrence GROW plans"
                                + " inputs for: it stays concrete"));
            }
        }
        int exposed = WaveGraph.writeGrowth(corpus, grown, unpaused, inputs,
                ZkEdges.of(corpus, chain), out);
        boolean fixpoint = open.empty() && exposed == 0
                && frontier.inFlightCount() == 0 && witnesses.isEmpty();
        if (fixpoint) {
            for (OccurrenceAddress paused : runWhole) {
                gaps.accept(GapRow.of(ExploreCodec.EXPLORATION,
                        GapKind.ADMISSION_GAP, GapClass.BLOCKING,
                        paused.render(), "demanded as a value and run for"
                                + " its doors alone by every session that"
                                + " captured it, and the exploration ends"
                                + " here: no replay ran it whole, so its"
                                + " guards and roots were never flippable"));
            }
        }
        for (OccurrenceAddress unexposed : waiting) {
            gaps.accept(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, fixpoint ? GapClass.BLOCKING
                            : GapClass.DIAGNOSTIC, unexposed.render(),
                    "only the seed replay ran this occurrence, under no "
                            + "planned task, and "
                            + (fixpoint ? "the exploration ends here: no "
                            + "focused replay ran it, so it is never a task"
                            : "the first admitted focused replay that runs "
                            + "it exposes it")));
        }
        RowCodec.writeAll(out.resolve(TASKS_FILE), tasks,
                ExploreCodec::writeTask);
        RowCodec.writeAll(out.resolve("obligations.jsonl"), open.obligations,
                ExploreCodec::writeObligation);
        String namingCut = corpus.namingCut();
        if (namingCut != null) {
            gaps.accept(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC, "arm keys",
                    namingCut));
        }
        gaps.write();
        JsonObject manifest = manifest(roots, tasks, why, frontier, open,
                topologyEpoch, gaps.byKind(), skeleton, exposed,
                truncated, ceilingCut, witnesses, wave(corpus), branches,
                concrete);
        manifest.add("openArms", openArms(corpus, roots, tasks, frontier,
                open, byFlip));
        manifest.add("boundedFlips", boundedFlips(iteration,
                frontier.boundedFlips()));
        manifest.add("force", forced.manifest);
        for (Parallel.Beside file : writing) file.join();
        writing.clear();
        Files.write(out.resolve(MANIFEST_FILE),
                (pretty(manifest) + System.lineSeparator())
                        .getBytes(StandardCharsets.UTF_8));
        slotsRound = round;
        return manifest;
    }

    private static Task anchorTask(List<Task> tasks,
                                   List<OccurrenceAddress> roots) {
        for (Task task : tasks) {
            if (roots.contains(task.focused())) return task;
        }
        return null;
    }

    static JsonArray openArms(Corpus corpus, List<OccurrenceAddress> roots,
                              List<Task> tasks, Frontier frontier,
                              Frontier.Round open,
                              Map<String, List<ObligationResult>> answers) {
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
                row.add("refused", ExploreCodec.list(new ArrayList<String>(
                        refusals.get(arm.getKey()))));
                arms.add(row);
            }
        }
        return arms;
    }

    static final String BOUNDED = "BOUNDED";

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
                    if (answer.verdict() == Verdict.DUPLICATE_WORLD) continue;
                    if (answer.verdict() == Verdict.ADMITTED) return "TAKEN";
                    if (answer.armRefusal() != null) {
                        refusals.add(answer.armRefusal());
                    }
                    if (answer.worldUnrefuted()) {
                        unrun.add(answer.obligationId() + "@"
                                + answer.sessionId());
                    }
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

    static Map<String, List<ObligationResult>> answersByFlip(Path iteration)
            throws IOException {
        Map<String, List<ObligationResult>> byFlip =
                new LinkedHashMap<String, List<ObligationResult>>();
        for (Answered worker : Parallel.map(ObligationDir.workerDirs(
                iteration), Answered::new, Parallel.directoriesAtOnce())) {
            if (worker.flip.isEmpty()) continue;
            byFlip.computeIfAbsent(worker.flip,
                    key -> new ArrayList<ObligationResult>())
                    .addAll(worker.results);
        }
        return byFlip;
    }

    private static final class Answered {
        final List<ObligationResult> results;
        final String flip;

        Answered(Path worker) throws IOException {
            this.results = RowCodec.readAll(
                    worker.resolve(ObligationDir.RESULT),
                    RowCodec::readObligationResult);
            this.flip = results.isEmpty() ? "" : flipOf(worker);
        }
    }

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

    private static int wave(Corpus corpus) throws IOException {
        Map<Path, Integer> waves = new LinkedHashMap<Path, Integer>();
        int deepest = 0;
        for (Map.Entry<String, Path> landed : corpus.landedIn().entrySet()) {
            if (corpus.session(landed.getKey()) == null) continue;
            Path round = landed.getValue();
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

    private static List<OccurrenceAddress> resolve(Corpus corpus,
                                                   String declaredAnchor,
                                                   List<GapRow> gaps) {
        String seed = corpus.seedSessionId();
        if (seed.isEmpty()) {
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

    private static Set<String> plannedOccurrences(Path iteration)
            throws IOException {
        Set<String> planned = new LinkedHashSet<String>();
        RowCodec.readEach(iteration.resolve("execution_task_plan.jsonl"),
                row -> row.has("occurrenceId")
                        ? row.get("occurrenceId").getAsString() : null,
                occurrence -> {
                    if (occurrence != null) planned.add(occurrence);
                });
        return planned;
    }

    private static Set<String> plannedInputs(Path iteration)
            throws IOException {
        Set<String> planned = new LinkedHashSet<String>();
        RowCodec.readEach(iteration.resolve("execution_task_plan.jsonl"),
                row -> {
                    List<String> inputs = new ArrayList<String>();
                    if (!row.has(InputActionCatalog.FIELD)) return inputs;
                    String taskId = row.has("taskId")
                            ? row.get("taskId").getAsString() : "";
                    for (JsonElement action
                            : row.getAsJsonArray(InputActionCatalog.FIELD)) {
                        JsonObject input = action.getAsJsonObject();
                        if (input.has("symbol")) {
                            inputs.add(taskId + " "
                                    + input.get("symbol").getAsString());
                        }
                    }
                    return inputs;
                }, planned::addAll);
        return planned;
    }

    private static Set<String> doorsOnlyOccurrences(Path iteration,
                                                    String mark)
            throws IOException {
        Set<String> doorsOnly = new LinkedHashSet<String>();
        RowCodec.readEach(iteration.resolve("execution_task_plan.jsonl"),
                row -> row.has(mark) && row.get(mark).getAsBoolean()
                        && row.has("occurrenceId")
                        ? row.get("occurrenceId").getAsString() : null,
                occurrence -> {
                    if (occurrence != null) doorsOnly.add(occurrence);
                });
        return doorsOnly;
    }

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
                                       Map<String, Integer> gaps,
                                       JsonObject skeleton,
                                       int exposed, int truncated,
                                       int ceilingCut,
                                       List<String> witnesses,
                                       int wave,
                                       Branches branches,
                                       Map<OccurrenceAddress,
                                               ClosurePlanner.Concrete>
                                               concrete) {
        JsonObject manifest = new JsonObject();
        JsonArray anchors = new JsonArray();
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
        manifest.addProperty("state", !open.empty() || exposed > 0
                ? "OBLIGATIONS_PROPOSED" : frontier.inFlightCount() > 0
                ? "AWAITING" : "FIXED_POINT");
        manifest.add("witnesses", ExploreCodec.list(witnesses));
        manifest.addProperty("inFlight", frontier.inFlightCount());
        manifest.addProperty("heldInFlight", open.heldInFlight);
        manifest.addProperty("branchesStopped", branches.stopped());
        manifest.addProperty("exposedRegions", exposed);
        manifest.addProperty("truncated", truncated);
        manifest.addProperty("ceilingCut", ceilingCut);
        manifest.add("skeleton", skeleton);
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
        for (Map.Entry<String, Integer> entry : gaps.entrySet()) {
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

    private static JsonObject skeleton(SlotTable slots,
                                       SlotTable.Reconciliation reconciled,
                                       RoundGaps gaps) {
        gaps.addAll(reconciled.gaps);
        JsonObject row = new JsonObject();
        row.addProperty("slots", slots.size());
        row.addProperty("opened", reconciled.opened.size());
        row.addProperty("filled", reconciled.filled);
        row.addProperty("outsideTheClosure", reconciled.outside);
        row.addProperty("replaced", reconciled.replaced);
        return row;
    }

    static List<GapRow> distinct(List<GapRow> gaps) {
        return new ArrayList<GapRow>(new LinkedHashSet<GapRow>(gaps));
    }

    static String pretty(JsonObject json) {
        return new GsonBuilder().disableHtmlEscaping().setPrettyPrinting()
                .create().toJson(json);
    }
}
