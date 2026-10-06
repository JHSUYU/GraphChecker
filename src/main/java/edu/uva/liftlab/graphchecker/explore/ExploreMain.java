package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.plan.SelectorResolution;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
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
import java.util.TreeSet;

/**
 * EXPLORE, one planner round: plan the closure, propose the flips still open.
 *
 * <pre>
 *   --sessions &lt;dir&gt;           the corpus; its parent is the iteration
 *   --target-occurrence &lt;sel&gt;  the case's declared anchor (v1 selector),
 *                              the ONE root of the closure
 *   --results &lt;file&gt;           earlier rounds' ObligationResults; an
 *                              answered query is never proposed again
 *   --in-flight &lt;file&gt;         the obligation rows the campaign has queued
 *                              or running; none is proposed again
 *   --static-scope-map &lt;file&gt;  the epoch's write/export sites and guards
 *                              (SYMBOL-SCOPE §3)
 *   --root-domains &lt;file&gt;      what the CASE says each root may be
 *   --round &lt;n&gt;                which round this is
 *   --topology-epoch &lt;id&gt;      the epoch these sessions belong to
 *   --output-dir &lt;dir&gt;         obligations.jsonl, tasks.jsonl, gaps.jsonl,
 *                              graph.jsonl, growth.jsonl,
 *                              explore_manifest.json
 *   --max-tasks / --max-paths-per-region / --max-flips-per-path /
 *   --max-world-depth
 * </pre>
 *
 * <p>ONE invocation is ONE round; the campaign owns the loop, the workers and
 * every stop (PIPELINE §7.9).  This rebuilds the frontier from every session,
 * recorded verdict and arm in flight, writes the unanswered flips, and states
 * the round's wave and the witnesses the corpus holds.  It never solves
 * ({@link ObligationSolverMain} does, one worker per obligation).</p>
 */
public final class ExploreMain {
    /** One round's manifest: its anchors, tasks and verdict counts. */
    static final String MANIFEST_FILE = "explore_manifest.json";

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
        JsonObject manifest = plan(iteration, declaredAnchor,
                options.path("root-domains"), options.path("results"),
                options.path("in-flight"), scopeMap, out,
                (int) options.number("round", 0),
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
     * Plans one round.
     *
     * @param declaredAnchor the case's v1 declaration,
     *                       the closure's only root (PIPELINE §7.1); resolved
     *                       against the seed here, so nothing downstream sees a
     *                       selector
     * @param inFlight       the obligation rows queued or running, or null
     *                       for none
     */
    public static JsonObject plan(Path iteration, String declaredAnchor,
                                  Path rootDomains, Path results,
                                  Path inFlight, Path scopeMap, Path out,
                                  int round, String topologyEpoch,
                                  int maxTasks,
                                  ObligationFactory.Bounds bounds)
            throws IOException {
        Corpus corpus = Corpus.read(iteration, rootDomains);
        StaticScopeMap scope = StaticScopeMap.read(scopeMap);
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
        Map<OccurrenceAddress, ClosurePlanner.Concrete> concrete =
                new LinkedHashMap<OccurrenceAddress,
                        ClosurePlanner.Concrete>();
        for (OccurrenceAddress root : roots) {
            ClosurePlanner.Plan plan = ClosurePlanner.plan(corpus, root,
                    maxTasks, scope, branches);
            gaps.addAll(plan.gaps);
            if (plan.concrete != null) concrete.put(root, plan.concrete);
            if (!plan.truncated.isEmpty()) {
                // A truncated closure misses arms, but whether that blocks a
                // claim is the exploration's end's to say: none once an
                // accepted witness ended it, else the closure it ended on
                // (the manifest's `truncated`, PIPELINE §7.9).  This round's
                // own is its record.
                truncated += plan.truncated.size();
                gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                        GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        root.render(), "closure truncated at " + maxTasks
                                + " tasks; " + plan.truncated.size()
                                + " occurrences were not planned, so this "
                                + "anchor's closure is incomplete: "
                                + plan.truncated));
            }
            for (Map.Entry<OccurrenceAddress, String> exposure
                    : plan.exposed.entrySet()) {
                grown.putIfAbsent(exposure.getKey(), exposure.getValue());
            }
            waiting.addAll(plan.waiting);
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
        // never empties the round (PIPELINE §7.1).
        SlotTable slots = SlotTable.read(iteration);
        SlotTable.Reconciliation skeleton = slots.reconcile(corpus, closure,
                round);
        gaps.addAll(skeleton.gaps);
        slots.write(iteration);

        // The one ledger of owed arms (Frontier).
        Frontier frontier = new Frontier(corpus, tasks, flipSites);
        frontier.consume(RowCodec.readAll(results,
                RowCodec::readObligationResult));
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
        Frontier.Round open = frontier.open(round, candidates);

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
        int exposed = WaveGraph.writeGrowth(corpus, grown, out);
        // What only the seed replay ran waits for a focused replay to expose
        // it -- unless this round is the fixpoint: then none ever will, and
        // the closure is incomplete.
        boolean fixpoint = open.empty() && exposed == 0
                && frontier.inFlightCount() == 0 && witnesses.isEmpty();
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
        RowCodec.writeAll(out.resolve("gaps.jsonl"), distinct(gaps),
                RowCodec::writeGap);
        JsonObject manifest = manifest(roots, tasks, why, frontier, open,
                topologyEpoch, gaps, slots, skeleton, exposed, truncated,
                witnesses, wave(iteration, corpus), branches, concrete);
        manifest.add("openArms", openArms(corpus, roots, tasks, frontier,
                open));
        Files.write(out.resolve(MANIFEST_FILE),
                (pretty(manifest) + System.lineSeparator())
                        .getBytes(StandardCharsets.UTF_8));
        return manifest;
    }

    /**
     * The open decider arms the declared anchor's reached, admitted runs left
     * phi without (TargetRow.OpenArm, causynth.BooleanReturns) and no run
     * took, each with what its flip came to on the paths that left it: a
     * path's flip TAKEN where a replay ran it ({@code ADMITTED}) or another
     * recorded path took it -- phi states the arm there, and an arm one path
     * took is not listed -- {@code UNSAT} where no world of the corpus takes
     * it, {@code UNANSWERED} where its flip came to anything else (a replay
     * that never reached the decision, NOT_ADMITTED), {@code PENDING} while
     * one is in flight, {@code NOT_ASKED} where no round cut it from that
     * path, {@code NOT_FLIPPABLE} where no decision under it states a
     * predicate.  The arm's state is the first of UNANSWERED, NOT_ASKED,
     * PENDING, NOT_FLIPPABLE, UNSAT any of its paths is in.  EMIT names each
     * (result.json concrete[] OPEN_ARM): an UNSAT closes over none but an
     * UNSAT one, and an UNANSWERED one leaves no verdict.
     */
    static JsonArray openArms(Corpus corpus, List<OccurrenceAddress> roots,
                              List<Task> tasks, Frontier frontier,
                              Frontier.Round open) {
        Set<String> proposed = new LinkedHashSet<String>();
        for (Obligation obligation : open.obligations) {
            proposed.add(obligation.obligationId());
        }
        String[] order = {"UNANSWERED", "NOT_ASKED", "PENDING",
                "NOT_FLIPPABLE", "UNSAT"};
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
            Set<String> taken = new LinkedHashSet<String>();
            for (TargetRow row : corpus.targetsOn(root)) {
                TargetRow.OpenArm arm = row.openArm();
                SessionReader session = corpus.session(row.sessionId());
                if (arm == null || !row.reachedAnchor() || session == null
                        || !session.admitted()) {
                    continue;
                }
                String key = arm.siteId() + "=" + arm.outcome();
                String state = openArmState(corpus, task, root, row, arm,
                        frontier, proposed);
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
                arms.add(row);
            }
        }
        return arms;
    }

    /** What one path's flip of its open arm came to ({@link #openArms}). */
    private static String openArmState(Corpus corpus, Task task,
                                       OccurrenceAddress root, TargetRow row,
                                       TargetRow.OpenArm arm,
                                       Frontier frontier,
                                       Set<String> proposed) {
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
                String id = ObligationFactory.obligationId(task.taskId(),
                        decision.siteId(), decision.ordinal(),
                        !decision.outcome(), ObligationFactory.dependence(
                                corpus, task, path, index));
                Verdict verdict = frontier.verdict(id);
                if (verdict == Verdict.ADMITTED || frontier.recorded(id)) {
                    return "TAKEN";
                }
                if (verdict == Verdict.UNSAT) return "UNSAT";
                if (verdict != null) return "UNANSWERED";
                return frontier.inFlight(id) || proposed.contains(id)
                        ? "PENDING" : "NOT_ASKED";
            }
        }
        return "NOT_ASKED";
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
        // Occurrences this round's closure did not plan (--max-tasks).
        manifest.addProperty("truncated", truncated);
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
