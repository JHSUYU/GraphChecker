package edu.uva.liftlab.graphchecker.runtime.d3;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.Obligation;
import edu.uva.liftlab.graphchecker.d3.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.SessionDir;
import edu.uva.liftlab.graphchecker.d3.contract.Task;
import edu.uva.liftlab.graphchecker.d3.contract.Verdict;
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
 * The focused-region replay: exactly one occurrence (or one state-connected
 * factor) runs symbolic, and every other region runs concretely with its
 * exports, attaches, writes and reads still recorded.
 *
 * <p>This is what replaces linked replay.  A linked replay coupled a
 * primary to its companions, so an unrelated prefix mismatch in a producer
 * region rejected the consumer's whole obligation -- 26 {@code
 * REPLAY_NOT_ADMITTED} on 11741 in one round.  Here admission evidence is
 * per focused region: the producer's exports are still recorded (they are
 * what the delivery states), and only the focused occurrence's own prefix
 * decides whether the obligation was admitted.</p>
 */
public final class FocusedReplay {
    /** Where the wave leaves this replay's task and obligations. */
    public static final String TASK_PROPERTY = "causynth.d3.task";

    private static final Object LOCK = new Object();
    private static boolean loaded;
    private static Task task;
    private static final List<Obligation> OBLIGATIONS =
            new ArrayList<Obligation>();
    /** obligationId -> the decisions the focused prefix must reproduce. */
    private static final Map<String, List<Expected>> PREFIXES =
            new LinkedHashMap<String, List<Expected>>();
    /** The interactions the epoch catalog states for the focused side. */
    private static final Set<String> CATALOG = new LinkedHashSet<String>();
    private static final Set<String> OBSERVED = new LinkedHashSet<String>();
    private static final Map<String, Integer> MATCHED =
            new LinkedHashMap<String, Integer>();
    private static final Map<String, String> REFUSALS =
            new LinkedHashMap<String, String>();
    private static final Set<String> FLIPPED = new LinkedHashSet<String>();
    /** The tasks this replay focuses, as the wave's plan rows name them. */
    private static final Set<String> FOCUSED_TASKS =
            new LinkedHashSet<String>();
    /** The occurrences those tasks turned out to be. */
    private static final Set<String> FOCUSED_OCCURRENCES =
            new LinkedHashSet<String>();

    private FocusedReplay() {
    }

    /** One expected decision of the focused prefix. */
    private static final class Expected {
        private final String siteId;
        private final int ordinal;
        private final boolean outcome;

        private Expected(String siteId, int ordinal, boolean outcome) {
            this.siteId = siteId;
            this.ordinal = ordinal;
            this.outcome = outcome;
        }

        private boolean is(String site, int k) {
            return siteId.equals(Text.safe(site)) && ordinal == k;
        }
    }

    /**
     * Whether this occurrence is the one that runs symbolic.
     *
     * <p>The focused occurrence, or one member of the state-connected
     * factor it is explored with -- writers and readers of one location on
     * one node, which cannot be explored apart without inventing a write
     * nobody made.</p>
     */
    public static boolean focused(OccurrenceAddress occurrence) {
        load();
        // A replay nothing focused -- the seed -- focuses nothing: every
        // occurrence of it ran as the plan had it, and the composer reads
        // the session whose activations are unfocused as the seed.
        if (occurrence == null) return false;
        synchronized (LOCK) {
            if (FOCUSED_OCCURRENCES.contains(occurrence.render())) {
                return true;
            }
        }
        if (task == null || task.focused() == null) return false;
        if (occurrence.equals(task.focused())) return true;
        if (task.factor() == null) return false;
        for (OccurrenceAddress member : task.factor()) {
            if (occurrence.equals(member)) return true;
        }
        return false;
    }

    /**
     * Whether this activation is the one the wave focused.
     *
     * <p>A wave's plan row names the TASK it focuses, not the address --
     * the address is what the replay finds out by running it.  So the first
     * activation of that task is the focused occurrence, and every later
     * row about it is focused by address.</p>
     */
    public static boolean focused(String taskId, OccurrenceAddress occurrence) {
        load();
        if (occurrence == null) return false;
        String id = Text.safe(taskId);
        synchronized (LOCK) {
            if (!id.isEmpty() && FOCUSED_TASKS.contains(id)) {
                FOCUSED_OCCURRENCES.add(occurrence.render());
                return true;
            }
        }
        boolean declared = focused(occurrence);
        if (declared) {
            synchronized (LOCK) {
                FOCUSED_OCCURRENCES.add(occurrence.render());
            }
        }
        return declared;
    }

    /** The value the wave assigned this root, or {@code ""}. */
    public static String rootAssignment(String rootId) {
        load();
        String id = Text.safe(rootId);
        for (Obligation obligation : OBLIGATIONS) {
            if (obligation.rootAssignments() == null) continue;
            String value = obligation.rootAssignments().get(id);
            if (value != null) return value;
        }
        return "";
    }

    /** The value the wave answered this attach endpoint with, or {@code ""}. */
    public static String answer(String endpointId) {
        load();
        String id = Text.safe(endpointId);
        for (Obligation obligation : OBLIGATIONS) {
            if (obligation.answers() == null) continue;
            String value = obligation.answers().get(id);
            if (value != null) return value;
        }
        return "";
    }

    /**
     * States one decision the focused occurrence took.
     *
     * <p>The prefix is matched in order: every decision before the flipped
     * one must reproduce, and the flipped one must take the flipped arm.
     * The first decision that does neither is the refusal, named with its
     * site -- "wrong decision at X" is a fact a reader can act on and
     * "not admitted" is not.</p>
     */
    public static void observeDecision(OccurrenceAddress occurrence,
                                       String siteId, int ordinal,
                                       boolean outcome) {
        load();
        if (task == null || !focused(occurrence)) return;
        synchronized (LOCK) {
            for (Obligation obligation : OBLIGATIONS) {
                observe(obligation, siteId, ordinal, outcome);
            }
        }
    }

    private static void observe(Obligation obligation, String siteId,
                                int ordinal, boolean outcome) {
        String id = Text.safe(obligation.obligationId());
        if (REFUSALS.containsKey(id) || FLIPPED.contains(id)) return;
        List<Expected> prefix = PREFIXES.get(id);
        int matched = MATCHED.containsKey(id) ? MATCHED.get(id) : 0;
        boolean flipSite = Text.safe(obligation.siteId()).equals(Text.safe(siteId))
                && obligation.ordinal() == ordinal;
        if (flipSite) {
            if (outcome == obligation.flippedOutcome()) {
                FLIPPED.add(id);
            } else {
                REFUSALS.put(id, "wrong decision at " + Text.safe(siteId)
                        + "#" + ordinal + ": took " + outcome
                        + ", the obligation flips it to "
                        + obligation.flippedOutcome());
            }
            return;
        }
        if (prefix == null || matched >= prefix.size()) return;
        Expected expected = prefix.get(matched);
        if (!expected.is(siteId, ordinal)) {
            // A decision the recorded prefix does not have at this position
            // is not yet a refusal: the prefix states the decisions of ONE
            // path and this occurrence may reach sites outside it.
            return;
        }
        if (expected.outcome != outcome) {
            REFUSALS.put(id, "wrong decision at " + Text.safe(siteId) + "#"
                    + ordinal + ": took " + outcome + ", the recorded prefix"
                    + " took " + expected.outcome);
            return;
        }
        MATCHED.put(id, matched + 1);
    }

    /**
     * Whether this occurrence has already contradicted its obligation.
     *
     * <p>The one prefix matcher: a replay is admitted or refused by what
     * {@link #observeDecision} has seen, and nothing else keeps a second
     * account of the same decisions.  A replay that was handed no
     * obligation contradicts nothing -- the seed decides by running.</p>
     */
    public static boolean contradicted(OccurrenceAddress occurrence) {
        load();
        if (task == null || !focused(occurrence)) return false;
        synchronized (LOCK) {
            for (Obligation obligation : OBLIGATIONS) {
                if (REFUSALS.containsKey(Text.safe(
                        obligation.obligationId()))) {
                    return true;
                }
            }
            return false;
        }
    }

    /** Why it was refused, for the row that says so. */
    public static String refusal(OccurrenceAddress occurrence) {
        load();
        if (task == null) return "";
        synchronized (LOCK) {
            for (Obligation obligation : OBLIGATIONS) {
                String detail = REFUSALS.get(Text.safe(
                        obligation.obligationId()));
                if (detail != null) return detail;
            }
            return "";
        }
    }

    /**
     * Whether this occurrence has taken the decision its obligation flips.
     *
     * <p>True for a replay with no obligation: there is no prefix to
     * complete, and a seed activation is never abandoned for one.</p>
     */
    public static boolean complete(OccurrenceAddress occurrence) {
        load();
        if (task == null || !focused(occurrence)) return true;
        synchronized (LOCK) {
            for (Obligation obligation : OBLIGATIONS) {
                if (!FLIPPED.contains(Text.safe(
                        obligation.obligationId()))) {
                    return false;
                }
            }
            return true;
        }
    }

    /** States one interaction endpoint the focused occurrence reached. */
    public static void observeInteraction(String endpointRender) {
        load();
        if (task == null) return;
        synchronized (LOCK) {
            OBSERVED.add(Text.safe(endpointRender));
        }
    }

    /**
     * What this replay settled, one row per obligation.
     *
     * <p>DIVERGED first: an interaction of the epoch catalog that did not
     * happen, or one that happened and is not in it, is a topology
     * divergence (R-I3) and the run's rows belong to the next epoch, not to
     * this obligation's verdict.</p>
     */
    public static List<ObligationResult> results(String sessionId) {
        load();
        List<ObligationResult> results = new ArrayList<ObligationResult>();
        if (task == null) return results;
        synchronized (LOCK) {
            String divergence = divergence();
            for (Obligation obligation : OBLIGATIONS) {
                String id = Text.safe(obligation.obligationId());
                if (!divergence.isEmpty()) {
                    results.add(ObligationResult.of(id, Verdict.DIVERGED,
                            sessionId, divergence));
                } else if (REFUSALS.containsKey(id)) {
                    results.add(ObligationResult.of(id, Verdict.NOT_ADMITTED,
                            sessionId, REFUSALS.get(id)));
                } else if (FLIPPED.contains(id)) {
                    results.add(ObligationResult.of(id, Verdict.ADMITTED,
                            sessionId, "the focused prefix reproduced and "
                            + Text.safe(obligation.siteId()) + "#"
                            + obligation.ordinal() + " took "
                            + obligation.flippedOutcome()));
                } else {
                    results.add(ObligationResult.of(id, Verdict.NOT_ADMITTED,
                            sessionId, "the focused occurrence never reached "
                            + Text.safe(obligation.siteId()) + "#"
                            + obligation.ordinal()));
                }
            }
        }
        return results;
    }

    /** The first catalogued interaction that is missing, or a new one. */
    private static String divergence() {
        if (CATALOG.isEmpty()) return "";
        for (String catalogued : CATALOG) {
            if (!OBSERVED.contains(catalogued)) {
                return "interaction of the epoch catalog did not happen: "
                        + catalogued;
            }
        }
        for (String observed : OBSERVED) {
            if (!CATALOG.contains(observed)) {
                return "interaction outside the epoch catalog happened: "
                        + observed;
            }
        }
        return "";
    }

    /** Where the campaign names this replay's execution task plan. */
    public static final String PLAN_PROPERTY = "causynth.concolic.task.plan";
    /** Where the campaign may name the focus row outright. */
    public static final String FOCUS_PROPERTY = "causynth.d3.focused.task";
    /** The file the obligation's solver worker writes the focus row into. */
    public static final String FOCUS_FILE = "focused_task.jsonl";

    /**
     * The focus row this replay was handed: one obligation's flip.
     *
     * <p>{@code d3.explore.ObligationSolverMain} writes {@code
     * focused_task.jsonl} with {@code taskId}, {@code obligationId}, {@code
     * pathId}, {@code focused} (the occurrence, rendered), {@code flip} =
     * {siteId, ordinal, outcome}, {@code rootAssignments}, {@code answers}
     * (attach endpoint id to value) and {@code unproducible}.  That row IS
     * the focused task: the replay applies the assignments at the mints of
     * the focused occurrence, the answers at its attaches, and enforces the
     * flip at the named decision.</p>
     *
     * <p>It is deliberately NOT {@code execution_task_plan.jsonl}: that name
     * belongs to the PLAN, whose rows are {@code d3.plan.ExecutionTask}s, and
     * the workload session opener decodes whatever stands under it.  One
     * file, one shape.  The row is looked for where the campaign says
     * ({@link #FOCUS_PROPERTY} or {@code CAUSYNTH_D3_FOCUSED_TASK}), else in
     * the worker directory, else beside the plan -- all three the same
     * directory in a campaign, so nothing new has to be wired.</p>
     */
    private static void loadPlanRows() {
        Path path = focusRow();
        if (path == null) return;
        try {
            for (JsonObject row : RowCodec.readJsonl(path)) {
                if (!row.has("flip") || !row.has("taskId")) continue;
                JsonObject flip = row.getAsJsonObject("flip");
                String obligationId = string(row, "obligationId");
                if (obligationId.isEmpty()) {
                    obligationId = string(row, "taskId");
                }
                OBLIGATIONS.add(Obligation.of(obligationId,
                        string(row, "taskId"), string(row, "pathId"),
                        string(flip, "siteId"),
                        flip.has("ordinal") ? flip.get("ordinal").getAsInt()
                                : 1,
                        flip.has("outcome")
                                && flip.get("outcome").getAsBoolean(),
                        strings(row, "rootAssignments"),
                        strings(row, "answers"),
                        list(row, "unproducible")));
                FOCUSED_TASKS.add(string(row, "taskId"));
                // The row states which occurrence it focuses, so the Task
                // this replay reports against is the recording's, not a stub
                // with no address.  Task.of refuses a null focus, which is
                // what a row without one now says rather than throwing on
                // the way out of this reader.
                OccurrenceAddress focus = occurrence(row.get("focused"));
                if (focus != null && focusedTask == null) {
                    List<OccurrenceAddress> members =
                            new ArrayList<OccurrenceAddress>();
                    if (row.has("factor")) {
                        for (JsonElement member
                                : row.getAsJsonArray("factor")) {
                            OccurrenceAddress parsed = occurrence(member);
                            if (parsed != null) members.add(parsed);
                        }
                    }
                    String seed = string(row, "seedSessionId");
                    if (seed.isEmpty()) {
                        seed = Text.safe(
                                System.getenv("CAUSYNTH_SEED_SESSION"));
                    }
                    if (!seed.isEmpty()) {
                        focusedTask = Task.of(string(row, "taskId"), focus,
                                members, seed);
                    }
                }
            }
        } catch (RuntimeException | IOException unreadable) {
            System.err.println("Causynth could not read the focus row "
                    + path + ": " + unreadable);
        }
        if (!OBLIGATIONS.isEmpty() && task == null && focusedTask != null) {
            task = focusedTask;
        }
    }

    /** The Task the focus row states, when it states one. */
    private static Task focusedTask;

    /** Where the focus row is, or null when this replay was handed none. */
    private static Path focusRow() {
        String named = Text.safe(System.getProperty(FOCUS_PROPERTY));
        if (named.isEmpty()) {
            named = Text.safe(System.getenv("CAUSYNTH_D3_FOCUSED_TASK"));
        }
        if (!named.isEmpty()) return readable(Paths.get(named));
        String worker = Text.safe(
                System.getenv("CAUSYNTH_CONCOLIC_WORKER_DIR"));
        if (!worker.isEmpty()) {
            Path inWorker = readable(Paths.get(worker).resolve(FOCUS_FILE));
            if (inWorker != null) return inWorker;
        }
        String plan = Text.safe(System.getProperty(PLAN_PROPERTY));
        if (plan.isEmpty()) {
            plan = Text.safe(System.getenv("CAUSYNTH_CONCOLIC_TASK_PLAN"));
        }
        if (plan.isEmpty()) return null;
        Path beside = Paths.get(plan).getParent();
        return beside == null ? null : readable(beside.resolve(FOCUS_FILE));
    }

    private static Path readable(Path file) {
        return Files.isReadable(file) ? file : null;
    }

    /** Reads the task file this replay was handed, once. */
    private static void load() {
        synchronized (LOCK) {
            if (loaded) return;
            loaded = true;
            loadPlanRows();
            String path = System.getProperty(TASK_PROPERTY);
            if (path == null || path.trim().isEmpty()) return;
            try {
                read(Paths.get(path.trim()));
            } catch (RuntimeException | IOException unreadable) {
                System.err.println("Causynth could not read the focused task "
                        + path + ": " + unreadable);
                task = null;
                OBLIGATIONS.clear();
            }
        }
    }

    /**
     * The file a wave hands one replay.
     *
     * <p>{@code {"task": {taskId, focused, factor[], seedSessionId},
     * "obligations": [{obligationId, taskId, pathId, siteId, ordinal,
     * flippedOutcome, rootAssignments{}, answers{}, unproducible[]}],
     * "prefix": {obligationId: [{siteId, ordinal, outcome}]},
     * "catalog": [endpoint id]}}, with every occurrence written the way
     * {@code RowCodec.writeOccurrence} writes one.  The prefix and the
     * catalog are optional: without a prefix the seed session's own
     * decisions are the prefix, which keeps one spelling of a recorded
     * fact.</p>
     */
    private static void read(Path file) throws IOException {
        String text = new String(Files.readAllBytes(file),
                StandardCharsets.UTF_8);
        JsonObject root = new JsonParser().parse(text).getAsJsonObject();
        JsonObject declared = root.getAsJsonObject("task");
        List<OccurrenceAddress> factor = new ArrayList<OccurrenceAddress>();
        if (declared.has("factor")) {
            for (JsonElement member : declared.getAsJsonArray("factor")) {
                factor.add(occurrence(member));
            }
        }
        task = Task.of(string(declared, "taskId"),
                occurrence(declared.get("focused")), factor,
                string(declared, "seedSessionId"));
        JsonArray obligations = root.has("obligations")
                ? root.getAsJsonArray("obligations") : new JsonArray();
        for (JsonElement element : obligations) {
            JsonObject obligation = element.getAsJsonObject();
            OBLIGATIONS.add(Obligation.of(
                    string(obligation, "obligationId"),
                    string(obligation, "taskId"),
                    string(obligation, "pathId"),
                    string(obligation, "siteId"),
                    obligation.has("ordinal")
                            ? obligation.get("ordinal").getAsInt() : 1,
                    obligation.has("flippedOutcome")
                            && obligation.get("flippedOutcome").getAsBoolean(),
                    strings(obligation, "rootAssignments"),
                    strings(obligation, "answers"),
                    list(obligation, "unproducible")));
        }
        if (root.has("catalog")) {
            for (JsonElement endpoint : root.getAsJsonArray("catalog")) {
                CATALOG.add(Text.safe(endpoint.getAsString()));
            }
        }
        if (root.has("prefix")) {
            for (Map.Entry<String, JsonElement> entry
                    : root.getAsJsonObject("prefix").entrySet()) {
                PREFIXES.put(Text.safe(entry.getKey()),
                        expected(entry.getValue().getAsJsonArray()));
            }
        }
        if (PREFIXES.isEmpty()) loadSeedPrefixes(file);
    }

    private static OccurrenceAddress occurrence(JsonElement element) {
        if (element == null || element.isJsonNull()) return null;
        if (element.isJsonPrimitive()) {
            return OccurrenceAddress.parse(element.getAsString());
        }
        return RowCodec.readOccurrence(element.getAsJsonObject());
    }

    private static String string(JsonObject row, String member) {
        return row.has(member) && !row.get(member).isJsonNull()
                ? row.get(member).getAsString() : "";
    }

    private static Map<String, String> strings(JsonObject row,
                                               String member) {
        Map<String, String> values = new LinkedHashMap<String, String>();
        if (!row.has(member) || row.get(member).isJsonNull()) return values;
        for (Map.Entry<String, JsonElement> entry
                : row.getAsJsonObject(member).entrySet()) {
            values.put(Text.safe(entry.getKey()),
                    entry.getValue().getAsString());
        }
        return values;
    }

    private static List<String> list(JsonObject row, String member) {
        List<String> values = new ArrayList<String>();
        if (!row.has(member) || row.get(member).isJsonNull()) return values;
        for (JsonElement value : row.getAsJsonArray(member)) {
            values.add(Text.safe(value.getAsString()));
        }
        return values;
    }

    private static List<Expected> expected(JsonArray decisions) {
        List<Expected> prefix = new ArrayList<Expected>();
        for (JsonElement decision : decisions) {
            JsonObject row = decision.getAsJsonObject();
            prefix.add(new Expected(
                    row.has("siteId") ? row.get("siteId").getAsString() : "",
                    row.has("ordinal") ? row.get("ordinal").getAsInt() : 0,
                    row.has("outcome") && row.get("outcome").getAsBoolean()));
        }
        return prefix;
    }

    /**
     * The focused occurrence's own decisions in the seed session, when the
     * wave stated no prefix of its own.
     *
     * <p>The prefix is a recorded fact of the seed, so reading it here
     * rather than restating it in the task file keeps one spelling of it.</p>
     */
    private static void loadSeedPrefixes(Path taskFile) {
        if (task == null || Text.safe(task.seedSessionId()).isEmpty()) return;
        Path iteration = D3Runtime.iterationOf(taskFile);
        if (iteration == null) return;
        Path decisions = SessionDir.of(iteration, task.seedSessionId())
                .decisions();
        if (!Files.isReadable(decisions)) return;
        List<Expected> prefix = new ArrayList<Expected>();
        try {
            for (JsonObject line : RowCodec.readJsonl(decisions)) {
                DecisionRow row = RowCodec.readDecision(line);
                if (row == null || !focused(row.occurrence())) continue;
                prefix.add(new Expected(row.siteId(), row.ordinal(),
                        row.outcome()));
            }
        } catch (IOException unreadable) {
            return;
        }
        for (Obligation obligation : OBLIGATIONS) {
            PREFIXES.put(Text.safe(obligation.obligationId()), prefix);
        }
    }

    /** Test hook: one task per fixture, read from {@code file}. */
    public static void loadForTests(Path file) {
        synchronized (LOCK) {
            resetForTests();
            loaded = true;
            try {
                read(file);
            } catch (RuntimeException | IOException unreadable) {
                throw new IllegalArgumentException(
                        "focused task is unreadable: " + unreadable, unreadable);
            }
        }
    }

    public static void resetForTests() {
        synchronized (LOCK) {
            loaded = false;
            task = null;
            OBLIGATIONS.clear();
            PREFIXES.clear();
            CATALOG.clear();
            OBSERVED.clear();
            MATCHED.clear();
            REFUSALS.clear();
            FLIPPED.clear();
            FOCUSED_TASKS.clear();
            FOCUSED_OCCURRENCES.clear();
        }
    }
}
