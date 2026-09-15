package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import java.io.IOException;
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
    private static final Object LOCK = new Object();
    private static boolean loaded;
    private static Task task;
    private static final List<Obligation> OBLIGATIONS =
            new ArrayList<Obligation>();
    private static final Set<String> OBSERVED = new LinkedHashSet<String>();
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

    /**
     * The skew the wave asks of this clock, or null when it asks none.
     *
     * <p>A clock is the one root every execution reads differently, so the
     * focus row states a DIFFERENCE and the mint adds it to the instant this
     * replay read.  Null and zero are different answers: zero is "read the
     * same instant the recording did", null is "the wave said nothing about
     * this clock".</p>
     */
    public static Long clockSkew(String rootId) {
        load();
        String stated = CLOCK_DELTAS.get(Text.safe(rootId));
        if (stated == null) return null;
        try {
            return Long.valueOf(stated);
        } catch (NumberFormatException notASkew) {
            return null;
        }
    }

    /** The skew the focus row states for each clock, by root id. */
    private static final Map<String, String> CLOCK_DELTAS =
            new LinkedHashMap<String, String>();

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
     * <p>The flipped decision must take the flipped arm.  A decision that
     * does not is the refusal, named with its site -- "wrong decision at X"
     * is a fact a reader can act on and "not admitted" is not.</p>
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
        if (!Text.safe(obligation.siteId()).equals(Text.safe(siteId))
                || obligation.ordinal() != ordinal) {
            return;
        }
        if (outcome == obligation.flippedOutcome()) {
            FLIPPED.add(id);
            return;
        }
        REFUSALS.put(id, "wrong decision at " + Text.safe(siteId)
                + "#" + ordinal + ": took " + outcome
                + ", the obligation flips it to "
                + obligation.flippedOutcome());
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
     * <p>Topology divergence is not decided here.  A flip that discovers a
     * topology this epoch does not have is EXPLORE's finding (rule E8),
     * read off the rows the replay published, and the runtime states no
     * second opinion about it.</p>
     */
    public static List<ObligationResult> results(String sessionId) {
        load();
        List<ObligationResult> results = new ArrayList<ObligationResult>();
        if (task == null) return results;
        synchronized (LOCK) {
            for (Obligation obligation : OBLIGATIONS) {
                String id = Text.safe(obligation.obligationId());
                if (REFUSALS.containsKey(id)) {
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

    /** Where the campaign names this replay's execution task plan. */
    public static final String PLAN_PROPERTY = "causynth.concolic.task.plan";
    /** The file the obligation's solver worker writes the focus row into. */
    public static final String FOCUS_FILE = "focused_task.jsonl";

    /**
     * The focus row this replay was handed: one obligation's flip.
     *
     * <p>{@code explore.ObligationSolverMain} writes {@code
     * focused_task.jsonl} with {@code taskId}, {@code obligationId}, {@code
     * pathId}, {@code focused} (the occurrence, rendered), {@code flip} =
     * {siteId, ordinal, outcome}, {@code rootAssignments}, {@code
     * clockDeltas} (root id to the skew to add to this replay's own
     * reading), {@code answers} (attach endpoint id to value) and {@code
     * unproducible}.  That row IS
     * the focused task: the replay applies the assignments at the mints of
     * the focused occurrence, the answers at its attaches, and enforces the
     * flip at the named decision.</p>
     *
     * <p>It is deliberately NOT {@code execution_task_plan.jsonl}: that name
     * belongs to the PLAN, whose rows are {@code plan.ExecutionTask}s, and
     * the workload session opener decodes whatever stands under it.  One
     * file, one shape.  The row is looked for in the worker directory the
     * campaign names, else beside the plan -- the same directory in a
     * campaign, so nothing new has to be wired.</p>
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
                CLOCK_DELTAS.putAll(strings(row, "clockDeltas"));
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

    /** Reads the focus row this replay was handed, once. */
    private static void load() {
        synchronized (LOCK) {
            if (loaded) return;
            loaded = true;
            loadPlanRows();
        }
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

    public static void resetForTests() {
        synchronized (LOCK) {
            loaded = false;
            task = null;
            OBLIGATIONS.clear();
            CLOCK_DELTAS.clear();
            OBSERVED.clear();
            REFUSALS.clear();
            FLIPPED.clear();
            FOCUSED_TASKS.clear();
            FOCUSED_OCCURRENCES.clear();
        }
    }
}
