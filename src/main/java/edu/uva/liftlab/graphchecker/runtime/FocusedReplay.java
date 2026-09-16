package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
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
    private static final Map<String, String> REFUSALS =
            new LinkedHashMap<String, String>();
    private static final Set<String> FLIPPED = new LinkedHashSet<String>();
    /** The tasks this replay focuses, as the wave's plan rows name them. */
    private static final Set<String> FOCUSED_TASKS =
            new LinkedHashSet<String>();
    /** The occurrences those tasks turned out to be. */
    private static final Set<String> FOCUSED_OCCURRENCES =
            new LinkedHashSet<String>();
    /**
     * The occurrence the recording mints each root this wave assigns at,
     * rendered, as the focus row's {@code rootMints} states them.
     *
     * <p>Focused for the same reason the flipped occurrence is: an
     * assignment is planted at the MINT and nowhere else
     * ({@code ConcolicRegionRuntime#focusedRootValue} asks only on a
     * focused occurrence), so a mint that runs unfocused reads the
     * recording's value under an obligation that asked for another one --
     * the {@code ASSIGNMENT_UNPLANTED} 31 of 11741 wave 0/1's obligations
     * met, their whole focused set being on the balancer while {@code
     * HDFS.BLOCK_KEY.SERIAL_NO} is minted in nn0's {@code
     * REGION.aaa1cfd7}.  A focused replay is one run of the whole workload,
     * so both are focused in the same run.</p>
     */
    private static final Set<String> ROOT_MINTS =
            new LinkedHashSet<String>();

    private FocusedReplay() {
    }

    /**
     * Whether this occurrence is one of the ones that run symbolic.
     *
     * <p>THE FOCUSED SET, and the one implementation of it: the focused
     * occurrence, one member of the state-connected factor it is explored
     * with -- writers and readers of one location on one node, which cannot
     * be explored apart without inventing a write nobody made -- or the
     * MINT of a root the obligation assigns ({@link #ROOT_MINTS}), because
     * a value is planted where the run mints it.</p>
     */
    public static boolean focused(OccurrenceAddress occurrence) {
        load();
        // A replay nothing focused -- the seed -- focuses nothing: every
        // occurrence of it ran as the plan had it, and the composer reads
        // the session whose activations are unfocused as the seed.
        if (occurrence == null) return false;
        synchronized (LOCK) {
            if (FOCUSED_OCCURRENCES.contains(occurrence.render())
                    || ROOT_MINTS.contains(occurrence.render())) {
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
     *
     * <p>AT THE OBLIGATION'S OWN OCCURRENCE.  The flip used to be addressed
     * by (siteId, ordinal) alone, and an ordinal restarts per activation:
     * four hdfs-11741 nodes run one {@code BlockTokenSecretManager}, so
     * {@code removeExpiredKeys#u15#1} happens on nn0, dn0, dn1 and the
     * balancer, and whichever ran first decided the obligation -- 6 of 11
     * campaign-#3 flips landed on the wrong node.  The occurrence's own
     * gate {@link #focused} does not narrow it either: it is true of every
     * member of the focused set, which includes each assigned root's MINT
     * and every factor member.</p>
     */
    public static void observeDecision(OccurrenceAddress occurrence,
                                       String siteId, int ordinal,
                                       boolean outcome) {
        load();
        if (task == null || occurrence == null) return;
        String at = occurrence.id();
        synchronized (LOCK) {
            for (Obligation obligation : OBLIGATIONS) {
                observe(obligation, at, siteId, ordinal, outcome);
            }
        }
    }

    private static void observe(Obligation obligation, String at,
                                String siteId, int ordinal,
                                boolean outcome) {
        String id = Text.safe(obligation.obligationId());
        if (REFUSALS.containsKey(id) || FLIPPED.contains(id)) return;
        // The focus row states which occurrence this obligation flips
        // ({@code focusedOccurrenceId}), and the contract's own identity is
        // what the two sides are joined on.
        if (!Text.safe(FOCUS.get(id)).equals(Text.safe(at))) return;
        if (!Text.safe(obligation.siteId()).equals(Text.safe(siteId))
                || obligation.ordinal() != ordinal) {
            return;
        }
        if (outcome == obligation.flippedOutcome()) {
            FLIPPED.add(id);
            return;
        }
        REFUSALS.put(id, "wrong decision at " + Text.safe(siteId)
                + "#" + ordinal + " of occurrence " + Text.safe(at)
                + ": took " + outcome + ", the obligation flips it to "
                + obligation.flippedOutcome());
    }

    /** Obligation id -> the occurrence id its flip is addressed at. */
    private static final Map<String, String> FOCUS =
            new LinkedHashMap<String, String>();

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
                } else if (Text.safe(FOCUS.get(id)).isEmpty()) {
                    // The row states no occurrence for the flip, so the
                    // flip is addressed at nothing and no decision of this
                    // replay could ever answer it.  Named, not read as
                    // "never reached": what is missing is the ask.
                    results.add(ObligationResult.of(id, Verdict.NOT_ADMITTED,
                            sessionId, "the focus row states no "
                            + "focusedOccurrenceId, so the flip at "
                            + Text.safe(obligation.siteId()) + "#"
                            + obligation.ordinal() + " is addressed at no "
                            + "occurrence of this replay"));
                } else {
                    results.add(ObligationResult.of(id, Verdict.NOT_ADMITTED,
                            sessionId, "occurrence "
                            + Text.safe(FOCUS.get(id)) + " never reached "
                            + Text.safe(obligation.siteId()) + "#"
                            + obligation.ordinal() + " in this replay"));
                }
            }
        }
        return results;
    }

    /** Where the campaign names this replay's execution task plan. */
    public static final String PLAN_PROPERTY = "causynth.concolic.task.plan";
    /**
     * The focus row this replay was handed: one obligation's flip.
     *
     * <p>{@code explore.ObligationSolverMain} writes {@code
     * focused_task.jsonl} with {@code taskId}, {@code obligationId}, {@code
     * pathId}, {@code focused} (the occurrence, rendered), {@code flip} =
     * {siteId, ordinal, outcome}, {@code rootAssignments}, {@code
     * clockDeltas} (root id to the skew to add to this replay's own
     * reading), {@code rootMints} (root id to the occurrence the recording
     * mints it at, which this replay focuses so that the assignment is
     * planted there), {@code answers} (attach endpoint id to value) and
     * {@code unproducible}.  That row IS
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
        // The role is decided HERE and by nothing else: a replay handed a
        // focus row is a FOCUSED replay, whatever it goes on to activate.
        handedAFocusRow = true;
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
                FOCUS.put(obligationId,
                        string(row, "focusedOccurrenceId"));
                CLOCK_DELTAS.putAll(strings(row, "clockDeltas"));
                // The mint of every assigned root is focused too, by
                // ADDRESS: the row states where the recording minted it,
                // and the assignment is planted there.
                for (Map.Entry<String, String> mint
                        : strings(row, "rootMints").entrySet()) {
                    OccurrenceAddress at =
                            OccurrenceAddress.parse(mint.getValue());
                    if (at != null) ROOT_MINTS.add(at.render());
                }
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

    /** Whether this replay was handed a focus row at all. */
    private static boolean handedAFocusRow;

    /**
     * Whether this replay is a FOCUSED one, rather than the recording.
     *
     * <p>The role this session STATES in its manifest.  It is "was I handed a
     * focus row", never "did I focus anything": a focused replay whose
     * occurrence never activated focused nothing and is still a focused
     * replay -- what it settled is its result row's to say.  Seven of the
     * 11741 campaign #2 sessions were exactly that, and reading them as
     * recordings left the corpus with nine candidate seeds.</p>
     */
    public static boolean focusedSession() {
        load();
        synchronized (LOCK) {
            return handedAFocusRow;
        }
    }

    /** The obligations this replay was handed, by id, in the row's order. */
    public static List<String> obligationIds() {
        load();
        List<String> ids = new ArrayList<String>();
        synchronized (LOCK) {
            for (Obligation obligation : OBLIGATIONS) {
                String id = Text.safe(obligation.obligationId());
                if (!id.isEmpty() && !ids.contains(id)) ids.add(id);
            }
        }
        return ids;
    }

    /**
     * Records that one mint of this replay planted the wave's value.
     *
     * <p>Filed where the value was actually WRITTEN, not where it was
     * decided: {@link #rootAssignment} is asked at every mint of the focused
     * occurrence and a mint that asked and could not place the write kept the
     * recording's value, which is a different fact.</p>
     */
    public static void planted(String rootId) {
        load();
        String id = Text.safe(rootId);
        if (id.isEmpty()) return;
        synchronized (LOCK) {
            PLANTED.add(id);
        }
    }

    /**
     * Every root the obligation assigns that no mint of this replay planted.
     *
     * <p>BLOCKING for this session, and stated by the REPLAY: a replay that
     * ran the recording's value under an obligation that asked for another
     * one did not run what was asked, and the composer meeting that as "the
     * mint states X and the obligation assigns Y" is the second statement of
     * it, not the first.  11741 session 869a1f0e285913ad-6f59cb84 is the
     * case: SERIAL_NO was minted through the field path, which never asked
     * for the wave's value at all.</p>
     */
    public static Map<String, String> unplantedAssignments() {
        load();
        Map<String, String> unplanted = new LinkedHashMap<String, String>();
        synchronized (LOCK) {
            for (Obligation obligation : OBLIGATIONS) {
                if (obligation.rootAssignments() == null) continue;
                for (Map.Entry<String, String> assigned
                        : obligation.rootAssignments().entrySet()) {
                    String id = Text.safe(assigned.getKey());
                    if (id.isEmpty() || PLANTED.contains(id)) continue;
                    unplanted.put(id, assigned.getValue());
                }
            }
        }
        return unplanted;
    }

    /** The roots a mint of this replay wrote the wave's value into. */
    private static final Set<String> PLANTED = new LinkedHashSet<String>();

    /** Where the focus row is, or null when this replay was handed none. */
    private static Path focusRow() {
        String worker = Text.safe(
                System.getenv("CAUSYNTH_CONCOLIC_WORKER_DIR"));
        if (!worker.isEmpty()) {
            Path inWorker = readable(Paths.get(worker).resolve(ObligationDir.FOCUSED_TASK));
            if (inWorker != null) return inWorker;
        }
        String plan = Text.safe(System.getProperty(PLAN_PROPERTY));
        if (plan.isEmpty()) {
            plan = Text.safe(System.getenv("CAUSYNTH_CONCOLIC_TASK_PLAN"));
        }
        if (plan.isEmpty()) return null;
        Path beside = Paths.get(plan).getParent();
        return beside == null ? null : readable(beside.resolve(ObligationDir.FOCUSED_TASK));
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
            handedAFocusRow = false;
            focusedTask = null;
            PLANTED.clear();
            ROOT_MINTS.clear();
            task = null;
            OBLIGATIONS.clear();
            CLOCK_DELTAS.clear();
            FOCUS.clear();
            REFUSALS.clear();
            FLIPPED.clear();
            FOCUSED_TASKS.clear();
            FOCUSED_OCCURRENCES.clear();
        }
    }
}
