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

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.setting;

/**
 * The focused-region replay: one occurrence (or one state-connected factor)
 * runs symbolic; every other region runs concretely with its rows still
 * recorded.
 *
 * <p>Admission is per focused occurrence: only its own prefix decides, so an
 * unrelated producer's prefix mismatch cannot reject the obligation.</p>
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
     * The mint occurrence of each assigned root (focus row {@code rootMints}),
     * by contract id.
     *
     * <p>Focused because an assignment is planted only at a focused MINT
     * ({@code RootMint#focusedRootValue}); an unfocused mint reads the
     * recording's value (ASSIGNMENT_UNPLANTED).</p>
     */
    private static final Set<String> ROOT_MINTS =
            new LinkedHashSet<String>();

    /**
     * One flip this replay INHERITED down the focus-row chain.
     *
     * <p>The replay runs in the world of the session its path was cut from
     * ({@code explore/Corpus.World}), so it is held to those flips with the
     * same (occurrence, site, ordinal) join as its own; the result row stays
     * the primary obligation's alone.</p>
     */
    private static final class Inherited {
        private final String at;
        private final String siteId;
        private final int ordinal;
        private final boolean outcome;
        private final String obligationId;
        /** Whether this replay has seen that occurrence take that arm. */
        private boolean taken;
        /** Why it cannot have, once it has taken the other one. */
        private String refusal = "";

        private Inherited(String at, String siteId, int ordinal,
                          boolean outcome, String obligationId) {
            this.at = at;
            this.siteId = siteId;
            this.ordinal = ordinal;
            this.outcome = outcome;
            this.obligationId = obligationId;
        }

        private String render() {
            return siteId + "#" + ordinal + " -> " + outcome
                    + " at occurrence " + at + " (obligation "
                    + obligationId + ")";
        }
    }

    /** The flips this replay inherited, in the focus row's order. */
    private static final List<Inherited> INHERITED =
            new ArrayList<Inherited>();

    /**
     * The inherited flips' occurrences, by contract id: focused so they plant
     * and publish, NEVER abandoned ({@link #complete}) -- a condition judged,
     * not a prefix driven to.
     */
    private static final Set<String> INHERITED_OCCURRENCES =
            new LinkedHashSet<String>();

    private FocusedReplay() {
    }

    /**
     * THE FOCUSED SET, its one implementation: the focused occurrence, its
     * state-connected factor (explored apart they would invent a write),
     * each assigned root's MINT ({@link #ROOT_MINTS}) and each inherited
     * flip's occurrence.
     */
    /** The case's declared occurrence, as the focus row states it, or "". */
    private static String declaredTarget = "";

    /**
     * Whether this is the case's declared occurrence: a focused replay that
     * observes the fatal there has answered its question
     * ({@code ConcolicResultPublisher#concludeAtWitness}).
     */
    static boolean declaredTarget(OccurrenceAddress occurrence) {
        load();
        if (occurrence == null) return false;
        synchronized (LOCK) {
            return !declaredTarget.isEmpty()
                    && declaredTarget.equals(occurrence.render());
        }
    }

    public static boolean focused(OccurrenceAddress occurrence) {
        load();
        // The seed focuses nothing.
        if (occurrence == null) return false;
        synchronized (LOCK) {
            if (FOCUSED_OCCURRENCES.contains(occurrence.render())
                    || ROOT_MINTS.contains(occurrence.id())
                    || INHERITED_OCCURRENCES.contains(occurrence.id())) {
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
     * Whether this activation is focused.  The plan row names a TASK; its
     * activation's address is learned here and focused from then on.
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
     * The skew (a DIFFERENCE added to this replay's reading) the wave asks of
     * this clock.  Zero is "the recording's instant"; null is "not asked".
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
     * States one decision; the flipped one must take the flipped arm, else
     * it is a refusal naming its site.
     *
     * <p>Joined on (occurrence, site, ordinal) at the obligation's OWN
     * occurrence: an ordinal restarts per activation, so (site, ordinal)
     * alone matches the same code on every node, and {@link #focused} is too
     * wide (the whole focused set).</p>
     *
     * @return whether this decision {@link #decide decided} the replay: it
     *         contradicted a flip the replay inherited
     */
    public static boolean observeDecision(OccurrenceAddress occurrence,
                                          String siteId, int ordinal,
                                          boolean outcome) {
        load();
        if (task == null || occurrence == null) return false;
        String at = occurrence.id();
        boolean decided = false;
        synchronized (LOCK) {
            for (Obligation obligation : OBLIGATIONS) {
                observe(obligation, at, siteId, ordinal, outcome);
            }
            // Same join for inherited flips; they only condition the
            // primary's admission ({@link #results}).
            for (Inherited flip : INHERITED) {
                if (flip.taken || !flip.refusal.isEmpty()) continue;
                if (!flip.at.equals(at)) continue;
                if (!flip.siteId.equals(Text.safe(siteId))
                        || flip.ordinal != ordinal) {
                    continue;
                }
                if (outcome == flip.outcome) {
                    flip.taken = true;
                    continue;
                }
                flip.refusal = "wrong decision at " + flip.siteId + "#"
                        + flip.ordinal + " of occurrence " + flip.at
                        + ": took " + outcome + ", the flip this replay "
                        + "INHERITED from the session its path was cut "
                        + "from is " + flip.render();
                decided |= decide(flip.refusal);
            }
        }
        return decided;
    }

    /**
     * THE EARLY END: the refusal that decided every obligation this replay
     * carries, or {@code ""} while one is still open.
     *
     * <p>Stated once, at the first refusal after which no obligation can end
     * anything but NOT_ADMITTED, whatever the run does next: the prefix of an
     * obligation's own occurrence abandoned ({@link #noteUnansweredTask}: it
     * took the recorded arm, or closed without the decision), which
     * {@link #unstated} holds against every flipped obligation, or a flip the
     * replay inherited contradicted, which {@link #inherited} holds against
     * every one.  A flipped obligation is never decided before its replay
     * ends: its session is a corpus session, and later waves and COMPOSE read
     * every row of it (the anchor, the fatal, writers after the anchor).</p>
     *
     * <p>A replay decided here ends at once
     * ({@code ConcolicResultPublisher#concludeAtRefusal}) and publishes no
     * session: its verdict rows name none ({@code RowRuntime#closeSession}),
     * and the campaign withdraws the directory it opened.  A NOT_ADMITTED
     * replay ran no world ({@code explore.ObligationFactory}), and rows cut
     * at the refusal are a prefix of a run no stage could tell from a whole
     * one.</p>
     */
    private static String refusedAt = "";

    /** States the refusal that decided this replay, once; called under
     *  {@link #LOCK}.  @return whether this call decided it. */
    private static boolean decide(String refusal) {
        if (!refusedAt.isEmpty() || OBLIGATIONS.isEmpty()) return false;
        refusedAt = refusal;
        return true;
    }

    /** The refusal that decided every obligation of this replay, or "". */
    static String refusedAt() {
        load();
        synchronized (LOCK) {
            return refusedAt;
        }
    }

    private static void observe(Obligation obligation, String at,
                                String siteId, int ordinal,
                                boolean outcome) {
        String id = Text.safe(obligation.obligationId());
        if (REFUSALS.containsKey(id) || FLIPPED.contains(id)) return;
        // Joined on the focus row's focusedOccurrenceId.
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
     * Whether this occurrence has contradicted ITS OWN obligation -- the one
     * prefix matcher, over what {@link #observeDecision} saw.
     *
     * <p>I2: a refusal abandons only its own occurrence, joined through
     * {@link #FOCUS} as {@link #observe} files it.  Trap: asking
     * {@link #focused} instead lets one refusal abandon every other member
     * of the focused set.</p>
     */
    public static boolean contradicted(OccurrenceAddress occurrence) {
        load();
        if (task == null || occurrence == null) return false;
        synchronized (LOCK) {
            return !refused(occurrence.id()).isEmpty();
        }
    }

    /** Why it was refused, for the row that says so. */
    public static String refusal(OccurrenceAddress occurrence) {
        load();
        if (task == null || occurrence == null) return "";
        synchronized (LOCK) {
            return refused(occurrence.id());
        }
    }

    /**
     * The refusal of an obligation addressed AT {@code at}, or {@code ""};
     * never another occurrence's.  Called under {@link #LOCK}.
     */
    private static String refused(String at) {
        for (Obligation obligation : OBLIGATIONS) {
            String id = Text.safe(obligation.obligationId());
            if (!Text.safe(FOCUS.get(id)).equals(Text.safe(at))) continue;
            String detail = REFUSALS.get(id);
            if (detail != null) return detail;
        }
        return "";
    }

    /**
     * Whether this occurrence has taken the decision ITS OWN obligation
     * flips; true when it has no obligation, or none is addressed at it.
     *
     * <p>The other half of I2, the same join as {@link #observe} (by id,
     * IDENTITY §10).
     * Trap: asked occurrence-blind, a root's mint or factor member is
     * abandoned for a flip it was never asked to take, and all its rows
     * (mint row included) are thrown away.</p>
     */
    public static boolean complete(OccurrenceAddress occurrence) {
        load();
        if (task == null || occurrence == null) return true;
        if (!focused(occurrence)) return true;
        String at = occurrence.id();
        synchronized (LOCK) {
            for (Obligation obligation : OBLIGATIONS) {
                String id = Text.safe(obligation.obligationId());
                if (!Text.safe(FOCUS.get(id)).equals(Text.safe(at))) continue;
                if (!FLIPPED.contains(id)) return false;
            }
            return true;
        }
    }

    /**
     * The gap that abandoned a prefix, if any.  An abandoned occurrence
     * publishes no rows, so {@link #FLIPPED} alone would admit over a
     * session missing its prefix.
     */
    private static String unmatchedPrefix = "";

    /** The reason a prefix abandonment opens its gap detail with. */
    private static final String PREFIX_UNMATCHED = "REPLAY_PREFIX_UNMATCHED";

    /** The reason a verdict opens with when a pairing the obligation's
     *  world plants was not taken: the run is not that world. */
    static final String PAIRING_UNTAKEN = "PAIRING_UNTAKEN";

    /**
     * Keeps the first prefix-abandonment gap, recognised by the reason word
     * it opens with ({@code ConcolicResultPublisher#taskUnanswered}).
     *
     * @return whether it {@link #decide decided} the replay
     */
    static boolean noteUnansweredTask(String detail) {
        String stated = Text.safe(detail);
        if (!stated.startsWith(PREFIX_UNMATCHED)) return false;
        load();
        synchronized (LOCK) {
            if (!unmatchedPrefix.isEmpty()) return false;
            unmatchedPrefix = stated;
            return decide(stated);
        }
    }

    /**
     * The publication the end of the run left running, if any
     * ({@code ConcolicResultPublisher#awaitSelectedResultPublications}): its
     * occurrence's rows may be partial, so the session carries no admission.
     */
    private static String unsettledPublication = "";

    /** Whether the run ended without a publication: its verdicts settle
     *  no question ({@code ObligationDir#QUESTION}). */
    static boolean unsettled() {
        synchronized (LOCK) {
            return !unsettledPublication.isEmpty();
        }
    }

    /** Notes the publication the run ended without; the first one stands. */
    static void noteUnsettledPublication(String detail) {
        load();
        synchronized (LOCK) {
            if (unsettledPublication.isEmpty()) {
                unsettledPublication = Text.safe(detail);
            }
        }
    }

    /** The roots this session PUBLISHED a mint row for. */
    private static final Set<String> MINTED = new LinkedHashSet<String>();

    /**
     * Notes one root mint ROW published.  Not {@link #planted}: a plant
     * survives an abandoned occurrence, the row does not, and the corpus
     * reads the row.
     */
    static void mintPublished(String rootId) {
        String id = Text.safe(rootId);
        if (id.isEmpty()) return;
        load();
        synchronized (LOCK) {
            MINTED.add(id);
        }
    }

    /**
     * What this replay settled, one row per obligation.  Topology divergence
     * is EXPLORE's finding (PIPELINE §7.1), not decided here.
     *
     * <p>FAIL-CLOSED: ADMITTED is a claim about the SESSION's rows, so the
     * flip alone does not admit -- an abandoned prefix, a missing mint row,
     * a broken inherited flip or a pairing its world plants and the run did
     * not take ({@link Confirmation#close}) is NOT_ADMITTED naming the gap.
     * A replay a refusal decided ({@link #refusedAt}) says in each detail
     * that it ended there.</p>
     */
    public static List<ObligationResult> results(String sessionId) {
        load();
        List<ObligationResult> results = new ArrayList<ObligationResult>();
        if (task == null) return results;
        // Asked outside this class's lock: Confirmation reads its rows under
        // its own, and asks this class whether it confirms.
        List<String> untaken = Confirmation.close();
        synchronized (LOCK) {
            for (ObligationResult result : settled(sessionId, untaken)) {
                results.add(refusedAt.isEmpty() ? result
                        : ObligationResult.of(result.obligationId(),
                                result.verdict(), result.sessionId(),
                                endedAtRefusal(result.detail())));
            }
        }
        return results;
    }

    /** One verdict's detail, and where the replay decided by
     *  {@link #refusedAt} ended.  Called under {@link #LOCK}. */
    private static String endedAtRefusal(String detail) {
        return detail + (refusedAt.contains(detail)
                ? "; the replay ended at this refusal and published no session"
                : "; the replay ended at the refusal that decided every"
                        + " obligation it carried and published no session: "
                        + refusedAt);
    }

    /** What each obligation settled; called under {@link #LOCK}. */
    private static List<ObligationResult> settled(String sessionId,
                                                  List<String> untaken) {
        List<ObligationResult> results = new ArrayList<ObligationResult>();
        for (Obligation obligation : OBLIGATIONS) {
            String id = Text.safe(obligation.obligationId());
            if (REFUSALS.containsKey(id)) {
                results.add(ObligationResult.of(id, Verdict.NOT_ADMITTED,
                        sessionId, REFUSALS.get(id)));
            } else if (FLIPPED.contains(id)) {
                // The one place ADMITTED is stated.
                String unstated = unstated(obligation);
                // And the inherited world has to hold, pairings and all
                // (a CONFIRM run's edges are its decision's to read).
                if (unstated.isEmpty()) unstated = inherited();
                if (unstated.isEmpty() && obligation.flips()
                        && !untaken.isEmpty()) {
                    unstated = PAIRING_UNTAKEN + ": the world this replay "
                            + "ran plants pairings it did not take: "
                            + String.join("; ", untaken);
                }
                results.add(unstated.isEmpty()
                        ? ObligationResult.of(id, Verdict.ADMITTED,
                                sessionId, obligation.flips()
                                ? "the focused prefix reproduced and "
                                + Text.safe(obligation.siteId()) + "#"
                                + obligation.ordinal() + " took "
                                + obligation.flippedOutcome()
                                : "the focused prefix reproduced and "
                                + "every root the model assigns was "
                                + "planted; no flip was owed")
                        : ObligationResult.of(id, Verdict.NOT_ADMITTED,
                                sessionId, unstated));
            } else if (Text.safe(FOCUS.get(id)).isEmpty()) {
                // No occurrence stated: the ask is missing, not the run.
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
        return results;
    }

    /**
     * Why the inherited world did not hold, or {@code ""}: a flip took the
     * other arm or was never reached.  Called under {@link #LOCK}.
     */
    private static String inherited() {
        for (Inherited flip : INHERITED) {
            if (!flip.refusal.isEmpty()) return flip.refusal;
        }
        for (Inherited flip : INHERITED) {
            if (!flip.taken) {
                return "this replay never reached the flip it INHERITED "
                        + "from the session its path was cut from: "
                        + flip.render();
            }
        }
        return "";
    }

    /**
     * Why the session cannot carry an admission, or {@code ""}: an abandoned
     * prefix, a publication the run ended without, or no mint row for an
     * assigned root or clock skew.  Called under {@link #LOCK}.
     */
    private static String unstated(Obligation obligation) {
        if (!unmatchedPrefix.isEmpty()) return unmatchedPrefix;
        if (!unsettledPublication.isEmpty()) return unsettledPublication;
        List<String> missing = new ArrayList<String>();
        if (obligation.rootAssignments() != null) {
            for (String rootId : obligation.rootAssignments().keySet()) {
                String id = Text.safe(rootId);
                if (!id.isEmpty() && !MINTED.contains(id)) missing.add(id);
            }
        }
        for (String rootId : CLOCK_DELTAS.keySet()) {
            String id = Text.safe(rootId);
            if (!id.isEmpty() && !MINTED.contains(id) && !missing.contains(id)) {
                missing.add(id);
            }
        }
        if (missing.isEmpty()) return "";
        return "this replay published no root mint row for " + missing
                + ", so its session states nothing about the value it ran"
                + " the root(s) the obligation moves at";
    }

    /** Where the campaign names this replay's execution task plan. */
    public static final String PLAN_PROPERTY = "causynth.concolic.task.plan";
    /**
     * Reads {@code focused_task.jsonl} ({@code explore.ObligationSolverMain}):
     * {@code taskId, obligationId, pathId, focused, flip={siteId, ordinal,
     * outcome}, rootAssignments, clockDeltas, rootMints, inheritedFlips,
     * answers, unproducible}.
     *
     * <p>Trap: not {@code execution_task_plan.jsonl} -- that name is the
     * PLAN's, and the session opener decodes whatever stands under it.</p>
     */
    private static void loadPlanRows() {
        Path path = focusRow();
        if (path == null) return;
        // The role is decided HERE: handed a focus row means FOCUSED.
        handedAFocusRow = true;
        // The Task the focus row states, when it states one.
        Task focusedTask = null;
        try {
            for (JsonObject row : RowCodec.readJsonl(path)) {
                if (!row.has("flip") || !row.has("taskId")) continue;
                String obligationId = optionalString(row, "obligationId");
                if (obligationId.isEmpty()) {
                    obligationId = optionalString(row, "taskId");
                }
                if (row.get("flip").isJsonNull()) {
                    // CONFIRM row (flip: null): roots planted, no decision
                    // owed, so it counts as flipped at load; agreement with
                    // the model is Confirmation's to read.
                    OBLIGATIONS.add(Obligation.confirming(obligationId,
                            optionalString(row, "taskId"),
                            optionalString(row, "pathId"),
                            strings(row, "rootAssignments"),
                            strings(row, "answers"),
                            list(row, "unproducible")));
                    FLIPPED.add(obligationId);
                } else {
                    JsonObject flip = row.getAsJsonObject("flip");
                    // A flip missing ordinal or outcome is refused, never
                    // defaulted, and stated as a shortfall at the close.
                    if (!flip.has("ordinal") || !flip.has("outcome")) {
                        SHORTFALLS.add("the focus row for obligation "
                                + obligationId + " states a flip with no "
                                + (flip.has("ordinal") ? "outcome"
                                : "ordinal")
                                + ", so this replay enforces no flip for it"
                                + " and answers it with no verdict");
                        continue;
                    }
                    OBLIGATIONS.add(Obligation.of(obligationId,
                            optionalString(row, "taskId"),
                            optionalString(row, "pathId"),
                            optionalString(flip, "siteId"),
                            flip.get("ordinal").getAsInt(),
                            flip.get("outcome").getAsBoolean(),
                            strings(row, "rootAssignments"),
                            strings(row, "answers"),
                            list(row, "unproducible")));
                }
                FOCUS.put(obligationId,
                        optionalString(row, "focusedOccurrenceId"));
                pairs |= !strings(row, "pairings").isEmpty();
                CLOCK_DELTAS.putAll(strings(row, "clockDeltas"));
                // Each assigned root's mint is focused too.
                for (Map.Entry<String, String> mint
                        : strings(row, "rootMints").entrySet()) {
                    OccurrenceAddress at =
                            OccurrenceAddress.parse(mint.getValue());
                    // By id(), not render(): a join across passes
                    // (IDENTITY §10).
                    if (at != null) ROOT_MINTS.add(at.id());
                }
                // Inherited flips, parent's first (see Inherited).
                if (row.has("inheritedFlips")
                        && !row.get("inheritedFlips").isJsonNull()) {
                    for (JsonElement element
                            : row.getAsJsonArray("inheritedFlips")) {
                        if (!element.isJsonObject()) continue;
                        JsonObject carried = element.getAsJsonObject();
                        if (!carried.has("ordinal") || !carried.has("outcome")) {
                            SHORTFALLS.add("the focus row for obligation "
                                    + obligationId + " states an inherited "
                                    + "flip at "
                                    + optionalString(carried, "siteId")
                                    + " with no "
                                    + (carried.has("ordinal") ? "outcome"
                                    : "ordinal") + ", so this replay cannot"
                                    + " be held to the world it was cut"
                                    + " from");
                            continue;
                        }
                        String at = optionalString(carried,
                                "focusedOccurrenceId");
                        INHERITED.add(new Inherited(at,
                                optionalString(carried, "siteId"),
                                carried.get("ordinal").getAsInt(),
                                carried.get("outcome").getAsBoolean(),
                                optionalString(carried, "obligationId")));
                        if (!at.isEmpty()) INHERITED_OCCURRENCES.add(at);
                    }
                }
                FOCUSED_TASKS.add(optionalString(row, "taskId"));
                if (declaredTarget.isEmpty()) {
                    declaredTarget = optionalString(row, "declaredTarget");
                }
                // Task.of refuses a null focus, so a row without one makes
                // no Task instead of throwing.
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
                    String seed = optionalString(row, "seedSessionId");
                    if (!seed.isEmpty()) {
                        focusedTask = Task.of(optionalString(row, "taskId"),
                                focus, members, seed);
                    }
                }
            }
        } catch (RuntimeException | IOException unreadable) {
            // Still FOCUSED with what it parsed; stated as a shortfall.
            SHORTFALLS.add("the focus row " + path + " could not be read"
                    + " whole (" + unreadable + "), so this session ran"
                    + " only the " + OBLIGATIONS.size() + " obligations it"
                    + " parsed before the fault");
        }
        if (!OBLIGATIONS.isEmpty() && task == null && focusedTask != null) {
            task = focusedTask;
        }
    }

    /**
     * What the focus row asked and could not be read; published by
     * {@code RowRuntime.closeSession}, since no publisher exists at load.
     */
    private static final List<String> SHORTFALLS = new ArrayList<String>();

    /** Every shortfall this replay's focus row left, in the order found. */
    static List<String> shortfalls() {
        load();
        synchronized (LOCK) {
            return new ArrayList<String>(SHORTFALLS);
        }
    }

    /** Whether this replay was handed a focus row at all. */
    private static boolean handedAFocusRow;

    /**
     * The manifest role: "handed a focus row", never "focused anything" --
     * a replay whose occurrence never ran is still no recording.
     */
    public static boolean focusedSession() {
        load();
        synchronized (LOCK) {
            return handedAFocusRow;
        }
    }

    /** Whether this replay's world plants pairings (the focus row's {@code
     *  pairings}): it owes the edges that hold it ({@link Confirmation}). */
    static boolean pairs() {
        load();
        synchronized (LOCK) {
            return pairs;
        }
    }

    /** Whether the focus row stated a pairing. */
    private static boolean pairs;

    /** Whether this replay confirms a claim: it was handed an obligation that
     *  flips nothing ({@link Obligation#confirming}). */
    static boolean confirming() {
        load();
        synchronized (LOCK) {
            for (Obligation obligation : OBLIGATIONS) {
                if (!obligation.flips()) return true;
            }
            return false;
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
     * Records that a mint WROTE the wave's value; asking
     * {@link #rootAssignment} and failing to write is a different fact.
     */
    public static void planted(String rootId) {
        load();
        String id = Text.safe(rootId);
        if (id.isEmpty()) return;
        synchronized (LOCK) {
            PLANTED.add(id);
        }
    }

    /** Notes that a mint of this root RAN, planted or not. */
    static void mintReached(String rootId) {
        String id = Text.safe(rootId);
        if (id.isEmpty()) return;
        load();
        synchronized (LOCK) {
            REACHED.add(id);
        }
    }

    /** The roots a mint site of this replay ran for. */
    private static final Set<String> REACHED = new LinkedHashSet<String>();

    /**
     * Every assigned root whose mint RAN and did not plant the wave's value
     * -- BLOCKING, stated by the replay because it did not run what was asked.
     *
     * <p>A mint that never ran is not one: the obligation's verdict names
     * that ({@link #results}).  One rule over both spellings, an absolute
     * {@code rootAssignment} and a {@code clockDelta} (reported as the skew
     * asked).</p>
     */
    public static Map<String, String> unplantedAssignments() {
        load();
        Map<String, String> unplanted = new LinkedHashMap<String, String>();
        synchronized (LOCK) {
            List<Map<String, String>> asked =
                    new ArrayList<Map<String, String>>();
            for (Obligation obligation : OBLIGATIONS) {
                if (obligation.rootAssignments() != null) {
                    asked.add(obligation.rootAssignments());
                }
            }
            asked.add(CLOCK_DELTAS);
            for (Map<String, String> roots : asked) {
                for (Map.Entry<String, String> assigned : roots.entrySet()) {
                    String id = Text.safe(assigned.getKey());
                    if (id.isEmpty() || PLANTED.contains(id)) continue;
                    if (!reachedLocked(id)) continue;
                    unplanted.put(id, assigned.getValue());
                }
            }
        }
        return unplanted;
    }

    /** The roots a mint of this replay wrote the wave's value into. */
    private static final Set<String> PLANTED = new LinkedHashSet<String>();

    /** Whether a mint of this root ran: it asked, or published its row. */
    private static boolean reachedLocked(String id) {
        return REACHED.contains(id) || MINTED.contains(id);
    }

    /** Where the focus row is, or null when this replay was handed none. */
    private static Path focusRow() {
        return workerFile(ObligationDir.FOCUSED_TASK);
    }

    /**
     * One file the worker handed this replay (focus row, {@link Confirmation}
     * edges), from the worker directory else beside the plan; or null.
     */
    static Path workerFile(String name) {
        String worker = workerDir();
        if (!worker.isEmpty()) {
            Path inWorker = readable(Paths.get(worker).resolve(name));
            if (inWorker != null) return inWorker;
        }
        String plan = setting(PLAN_PROPERTY, "CAUSYNTH_CONCOLIC_TASK_PLAN");
        if (plan.isEmpty()) return null;
        Path beside = Paths.get(plan).getParent();
        return beside == null ? null : readable(beside.resolve(name));
    }

    /** The directory the campaign hands this replay's worker, or "". */
    static String workerDir() {
        return Text.safe(System.getenv("CAUSYNTH_CONCOLIC_WORKER_DIR"));
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
            pairs = false;
            PLANTED.clear();
            MINTED.clear();
            REACHED.clear();
            unmatchedPrefix = "";
            unsettledPublication = "";
            refusedAt = "";
            ROOT_MINTS.clear();
            task = null;
            OBLIGATIONS.clear();
            CLOCK_DELTAS.clear();
            FOCUS.clear();
            REFUSALS.clear();
            FLIPPED.clear();
            FOCUSED_TASKS.clear();
            declaredTarget = "";
            FOCUSED_OCCURRENCES.clear();
            INHERITED.clear();
            INHERITED_OCCURRENCES.clear();
            SHORTFALLS.clear();
        }
    }
}
