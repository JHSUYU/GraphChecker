package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadsFrom;
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
    /** The versions the focus rows' world chose ({@link Versions}). */
    private static final List<ReadsFrom> VERSIONS =
            new ArrayList<ReadsFrom>();
    /** The tasks this replay focuses, as the wave's plan rows name them. */
    private static final Set<String> FOCUSED_TASKS =
            new LinkedHashSet<String>();
    /** The occurrences those tasks turned out to be. */
    private static final Set<String> FOCUSED_OCCURRENCES =
            new LinkedHashSet<String>();
    /**
     * The occurrence the recording mints each root this wave assigns at, by
     * the contract's own id, off the focus row's {@code rootMints}.
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

    /**
     * One decision this replay INHERITED: its parent's flip, or one of
     * theirs, carried down the chain by the focus row.
     *
     * <p>A focused replay runs inside the world of the session its path was
     * cut from ({@code explore/Corpus.World}), and the flips that session
     * was held to are part of that world: 11741's witness is dn1's expiry
     * compare flipped a second time on a refresh path that exists only
     * because nn0's rotation stopped exporting the key.  So the replay is
     * held to every one of them, exactly as it is to its own flip -- same
     * (occurrence, site, ordinal) join, same refusal on the wrong arm --
     * while the RESULT ROW it publishes stays the primary obligation's
     * alone, because one worker answers one verdict.</p>
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
     * The occurrences those flips are addressed at, by the contract's id.
     *
     * <p>Focused, so their mints plant and their decisions are published --
     * and NEVER abandoned: {@link #complete} asks only the primary flip's
     * own occurrence, because an inherited flip is a condition this replay
     * is judged on and not a prefix it is driven to.</p>
     */
    private static final Set<String> INHERITED_OCCURRENCES =
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
            // THE SAME JOIN for a flip this replay inherited: the occurrence
            // the focus row addresses it at, its site and its ordinal.  It
            // refuses nothing and abandons nothing -- it is a condition on
            // the ADMISSION of the primary obligation, answered in
            // {@link #results}.
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
     * Whether this occurrence has already contradicted ITS OWN obligation.
     *
     * <p>The one prefix matcher: a replay is admitted or refused by what
     * {@link #observeDecision} has seen, and nothing else keeps a second
     * account of the same decisions.  A replay that was handed no
     * obligation contradicts nothing -- the seed decides by running.</p>
     *
     * <p>I2 -- A REFUSAL ABANDONS ONLY ITS OWN OCCURRENCE, and the
     * obligation's own occurrence is the one its focus row addresses
     * ({@link #FOCUS}), which is the same join {@link #observe} takes when
     * it FILES the refusal.  This asked {@link #focused} instead, which is
     * true of every member of the focused set -- each assigned root's mint,
     * every factor member, every occurrence an inherited flip named -- so
     * one obligation's refusal abandoned the next focused activation at its
     * first decision: {@code BranchObservation#observe} finishes it
     * REPLAY_PREFIX_CONTRADICTED, {@code closeOccurrence} publishes none of
     * its rows, and the Java call keeps running inside the still-live
     * enclosing activation.  10 of hdfs-11741's 40 nn0-focused sessions show
     * that migration, always on the node of {@code inheritedFlips[0]}, and
     * it makes an inherited flip read as "never reached" by luck.</p>
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
     * The refusal filed against an obligation addressed AT {@code at}.
     *
     * <p>Called under {@link #LOCK}.  {@code ""} is "no obligation of this
     * occurrence is refused", which includes "this occurrence carries no
     * obligation at all" -- another obligation's refusal is not this
     * occurrence's to answer for.</p>
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
     * flips.
     *
     * <p>True for a replay with no obligation: there is no prefix to
     * complete, and a seed activation is never abandoned for one.  True as
     * well for a focused occurrence NO obligation's flip is addressed at:
     * the question is not asked of it, so it has no failing answer.</p>
     *
     * <p>THE SAME JOIN {@link #observe} TAKES (R4a), on the other side of
     * it.  A decision is credited to the obligation whose {@code
     * focusedOccurrenceId} it happened at, so the terminal that answers the
     * obligation is that same occurrence's -- and the FOCUSED SET is
     * wider than it: every factor member, and the MINT of each assigned
     * root.  Asked occurrence-blind, this refused the flip's own question
     * at a mint's terminal, and {@code judgeFinishedOccurrence} abandoned
     * the mint -- which throws away every row that occurrence published.
     * HDFS-17960 on 39bedd768, obligation {@code 793875fb482a10a4}: its
     * flip is at {@code applyEditLogOp@8/deleteSnapshot} ({@code
     * focusedOccurrenceId ea10d7e883e23973}) and its {@code rootMints}
     * name {@code applyEditLogOp@7/deleteSnapshot} ({@code
     * 4786cb8a1d2bd655}), a DIFFERENT occurrence.  The mint at @7 finished
     * first, its own flip had not happened and could not have, and the
     * replay abandoned it: 42 decision rows and the session's ONLY root
     * mint row went with it, leaving a 0-byte {@code roots.jsonl}.  The
     * sibling obligation {@code cb67875d1d896d4d}, whose flip and mint are
     * the same occurrence, kept everything in the same wave.</p>
     *
     * <p>AND TRUE FOR EVERY OTHER MEMBER OF THE FOCUSED SET.  Only the
     * flip's OWN occurrence can complete it -- the same join {@link #observe}
     * takes, on the other side of it -- so only that one is asked here: a
     * root's mint, a factor member and the occurrence of a flip this replay
     * INHERITED are focused so that they plant and publish, and abandoning
     * one of them for a decision it was never asked to take would throw
     * away every row it published.</p>
     *
     * <p>The other half of I2, and the same join: an occurrence is
     * abandoned for the flip IT was asked to take and for no other
     * obligation's.</p>
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
     * The prefix this replay was abandoned on, as the gap that named it.
     *
     * <p>An abandoned occurrence publishes NO rows -- that is what
     * abandoning one means -- so the session it leaves behind is missing
     * every decision, read, write and mint that occurrence made.  The one
     * account of the replay therefore has to hold it: a verdict read off
     * {@link #FLIPPED} alone says "the focused prefix reproduced" over a
     * session whose prefix is not in it.</p>
     */
    private static String unmatchedPrefix = "";

    /** The reason a prefix abandonment opens its gap detail with. */
    private static final String PREFIX_UNMATCHED = "REPLAY_PREFIX_UNMATCHED";

    /**
     * Notes one unanswered-task gap, and keeps the prefix ones.
     *
     * <p>Every such gap opens with its reason
     * ({@code ConcolicResultPublisher#taskUnanswered}), and the reason is
     * the field: what this reads is the word the row states, not a shape it
     * guessed.  Anything but a prefix abandonment is a fact about a task
     * and not about this replay's obligations, and is ignored here.</p>
     */
    static void noteUnansweredTask(String detail) {
        String stated = Text.safe(detail);
        if (!stated.startsWith(PREFIX_UNMATCHED)) return;
        load();
        synchronized (LOCK) {
            if (unmatchedPrefix.isEmpty()) unmatchedPrefix = stated;
        }
    }

    /** The roots this session PUBLISHED a mint row for. */
    private static final Set<String> MINTED = new LinkedHashSet<String>();

    /**
     * Notes one root mint ROW this session published.
     *
     * <p>Told apart from {@link #planted} on purpose: that one says the
     * wave's value reached the field, this one says the SESSION states the
     * mint.  A replay can do the first and not the second -- the mint's
     * occurrence is abandoned after the plant -- and it is the second the
     * corpus is read on.</p>
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
     * What this replay settled, one row per obligation.
     *
     * <p>Topology divergence is not decided here.  A flip that discovers a
     * topology this epoch does not have is EXPLORE's finding (rule E8),
     * read off the rows the replay published, and the runtime states no
     * second opinion about it.</p>
     *
     * <p>FAIL-CLOSED, ONE RULE.  ADMITTED means "the focused prefix
     * reproduced and the flip took the other arm", and that is a claim
     * about the SESSION -- the rows a later stage reads.  So the flip alone
     * does not admit: a replay whose focused prefix was abandoned, or whose
     * session states no mint row for a root the wave assigned, states
     * NOT_ADMITTED naming the gap, because the evidence for the sentence is
     * not in the corpus.  The 39bedd768 HDFS-17960 session {@code
     * 793875fb482a10a4-4b39d011} is both at once: a 0-byte {@code
     * roots.jsonl}, its flip occurrence's 42 rows gone with the
     * REPLAY_PREFIX_UNMATCHED gap that abandoned them, and {@code
     * obligation_result.jsonl} reading ADMITTED.</p>
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
                    // The one place an ADMITTED is stated, and the only
                    // thing this gate does is refuse one: every other
                    // verdict below keeps the words it already had.
                    String unstated = unstated(obligation);
                    // AND THE WORLD HAS TO HOLD.  A replay whose inherited
                    // flip was contradicted, or never reached at all, ran
                    // in a world other than the one its path was cut from,
                    // so the path it recorded is not the path the next wave
                    // would cut from it; and one whose held reads did not
                    // observe the versions its world chose ran another
                    // interleaving than the one it was asked about.
                    if (unstated.isEmpty()) unstated = inherited();
                    if (unstated.isEmpty()) unstated = Versions.unrealized();
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

    /**
     * Why this replay's session cannot carry an admission, or {@code ""}.
     *
     * <p>Two ways, and both are "the rows are not there to be read".  A
     * prefix this replay was abandoned on took the abandoned occurrence's
     * whole row set with it.  A root the wave assigned whose mint row the
     * session does not state leaves the valuation the replay ran unstated
     * in the corpus -- over BOTH spellings of what a wave asks of a root,
     * an absolute assignment and a clock's skew, for the reason {@link
     * #unplantedAssignments} gives.</p>
     *
     * <p>Called under {@link #LOCK}.</p>
     */
    /**
     * Why the world this replay inherited did not hold, or {@code ""}.
     *
     * <p>Two ways, and the row names which flip it was either way: the
     * occurrence took the other arm, or it never took that decision at all.
     * Both say the path this replay recorded is not a path of the world the
     * obligation was cut from.</p>
     *
     * <p>Called under {@link #LOCK}.</p>
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

    private static String unstated(Obligation obligation) {
        if (!unmatchedPrefix.isEmpty()) return unmatchedPrefix;
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
     * The focus row this replay was handed: one obligation's flip.
     *
     * <p>{@code explore.ObligationSolverMain} writes {@code
     * focused_task.jsonl} with {@code taskId}, {@code obligationId}, {@code
     * pathId}, {@code focused} (the occurrence, rendered), {@code flip} =
     * {siteId, ordinal, outcome}, {@code rootAssignments}, {@code
     * clockDeltas} (root id to the skew to add to this replay's own
     * reading), {@code rootMints} (root id to the occurrence the recording
     * mints it at, which this replay focuses so that the assignment is
     * planted there), {@code inheritedFlips} (the flips of the session this
     * obligation's path was cut from, each {focusedOccurrenceId, siteId,
     * ordinal, outcome, obligationId}), {@code answers} (attach endpoint id
     * to value) and {@code unproducible}.  That row IS
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
                String obligationId = string(row, "obligationId");
                if (obligationId.isEmpty()) {
                    obligationId = string(row, "taskId");
                }
                if (row.get("flip").isJsonNull()) {
                    // A CONFIRM row: {@code flip: null}.  The model's roots
                    // are planted and the selected path's schedule held
                    // exactly as for a flip, and NO decision is owed the
                    // other arm -- the values drive them.  So the
                    // obligation is taken at load: {@link #complete} never
                    // abandons the anchor for a decision it was not asked
                    // to take, and {@link #results} admits it by its
                    // plants and its prefix alone.  Whether the run agreed
                    // with the model is what {@link Confirmation} reads off
                    // the rows.
                    OBLIGATIONS.add(Obligation.confirming(obligationId,
                            string(row, "taskId"), string(row, "pathId"),
                            strings(row, "rootAssignments"),
                            strings(row, "answers"),
                            list(row, "unproducible")));
                    FLIPPED.add(obligationId);
                } else {
                    JsonObject flip = row.getAsJsonObject("flip");
                    // The flip IS the obligation: which decision, which
                    // occurrence of it, and which arm.  A row that states
                    // no ordinal or no outcome used to be read as
                    // "occurrence 1, arm false", so the replay enforced a
                    // flip nothing asked for and published its verdict as
                    // though it had run the obligation.  Every focus row
                    // missing either member is refused here and the
                    // shortfall is stated at the close.
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
                            string(row, "taskId"), string(row, "pathId"),
                            string(flip, "siteId"),
                            flip.get("ordinal").getAsInt(),
                            flip.get("outcome").getAsBoolean(),
                            strings(row, "rootAssignments"),
                            strings(row, "answers"),
                            list(row, "unproducible")));
                }
                FOCUS.put(obligationId,
                        string(row, "focusedOccurrenceId"));
                CLOCK_DELTAS.putAll(strings(row, "clockDeltas"));
                if (row.has("versions") && row.get("versions").isJsonArray()) {
                    for (JsonElement version
                            : row.getAsJsonArray("versions")) {
                        VERSIONS.add(RowCodec.readReadsFrom(
                                version.getAsJsonObject()));
                    }
                }
                // The mint of every assigned root is focused too, by
                // ADDRESS: the row states where the recording minted it,
                // and the assignment is planted there.
                for (Map.Entry<String, String> mint
                        : strings(row, "rootMints").entrySet()) {
                    OccurrenceAddress at =
                            OccurrenceAddress.parse(mint.getValue());
                    // BY THE CONTRACT'S IDENTITY, not by the rendered
                    // string: the render is a spelling of the parts and
                    // this is a join between two passes, which is what
                    // OccurrenceAddress.id() is for.  The same join the
                    // flip takes (FOCUS, R4a).
                    if (at != null) ROOT_MINTS.add(at.id());
                }
                // THE FLIPS THIS REPLAY INHERITED, in the row's order: its
                // parent's own flip first, then the ones its parent
                // inherited.  Their occurrences are focused so their mints
                // plant and their decisions are published; they are never
                // abandoned ({@link #complete}) and they answer no result
                // row of their own -- they are conditions on the primary
                // obligation's admission.
                if (row.has("inheritedFlips")
                        && !row.get("inheritedFlips").isJsonNull()) {
                    for (JsonElement element
                            : row.getAsJsonArray("inheritedFlips")) {
                        if (!element.isJsonObject()) continue;
                        JsonObject carried = element.getAsJsonObject();
                        if (!carried.has("ordinal") || !carried.has("outcome")) {
                            SHORTFALLS.add("the focus row for obligation "
                                    + obligationId + " states an inherited "
                                    + "flip at " + string(carried, "siteId")
                                    + " with no "
                                    + (carried.has("ordinal") ? "outcome"
                                    : "ordinal") + ", so this replay cannot"
                                    + " be held to the world it was cut"
                                    + " from");
                            continue;
                        }
                        String at = string(carried, "focusedOccurrenceId");
                        INHERITED.add(new Inherited(at,
                                string(carried, "siteId"),
                                carried.get("ordinal").getAsInt(),
                                carried.get("outcome").getAsBoolean(),
                                string(carried, "obligationId")));
                        if (!at.isEmpty()) INHERITED_OCCURRENCES.add(at);
                    }
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
            // handedAFocusRow is already true, so this session publishes
            // role FOCUSED with however many obligations it parsed before
            // the fault.  On stderr that was invisible to every reader of
            // the corpus; the session states it as its own shortfall.
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
     * What this replay was asked for and could not read, for the rows that
     * state it (published by {@code RowRuntime.closeSession}).
     *
     * <p>Not filed as a gap here: this runs inside the session open, before
     * the publisher exists, so a row written now is a row nothing writes.
     * </p>
     */
    private static final List<String> SHORTFALLS = new ArrayList<String>();

    /** Every shortfall this replay's focus row left, in the order found. */
    static List<String> shortfalls() {
        load();
        synchronized (LOCK) {
            return new ArrayList<String>(SHORTFALLS);
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
     * Notes that a mint site of this root RAN in this replay, whether or not
     * it then planted the wave's value -- the fact that tells an unplanted
     * assignment from one whose mint never came.
     */
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
     * Every root the obligation assigns whose mint RAN in this replay and did
     * not plant the wave's value.
     *
     * <p>BLOCKING for this session, and stated by the REPLAY: a replay that
     * ran the recording's value under an obligation that asked for another
     * one did not run what was asked, and the composer meeting that as "the
     * mint states X and the obligation assigns Y" is the second statement of
     * it, not the first.  11741 session 869a1f0e285913ad-6f59cb84 is the
     * case: SERIAL_NO was minted through the field path, which never asked
     * for the wave's value at all.</p>
     *
     * <p>A root whose mint never ran is not one: nothing read the
     * recording's value in its place, because nothing read it at all.  The
     * occurrence the obligation was for did not happen in this run, and the
     * obligation's own verdict states that -- NOT_ADMITTED, naming the
     * occurrence never reached or the mint row the session lacks
     * ({@link #results}).  hdfs-17967 path B reported five such "unplanted"
     * assignments as blockers, each the input of an addKeys occurrence its
     * replay never ran.</p>
     *
     * <p>ONE RULE OVER BOTH SPELLINGS of what a wave asks of a root: an
     * absolute {@code rootAssignment} and a {@code clockDelta}.  It covered
     * the assignments only, and a clock is the root ELEVEN of hdfs-11741
     * campaign #3's twelve obligations ask about -- six of them state a
     * delta that no mint of their replay ever planted (their clock's mint
     * row is absent from the session altogether), and every one of those
     * six was silent.  A delta is reported as the SKEW that was asked,
     * because that is what the row states; the instant it would have
     * produced is the replay's own reading plus it, and the replay did not
     * make one.</p>
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
                    if (!reachedLocked(id)) continue;
                    unplanted.put(id, assigned.getValue());
                }
            }
            for (Map.Entry<String, String> skew : CLOCK_DELTAS.entrySet()) {
                String id = Text.safe(skew.getKey());
                if (id.isEmpty() || PLANTED.contains(id)) continue;
                if (!reachedLocked(id)) continue;
                unplanted.put(id, skew.getValue());
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
     * One file of the worker directory this replay was handed, or null.
     *
     * <p>The one lookup for everything a worker hands its replay: the
     * focus row, and the expected edges of a CONFIRM run
     * ({@link Confirmation}).  In the worker directory the campaign names,
     * else beside the plan -- the same directory in a campaign.</p>
     */
    static Path workerFile(String name) {
        String worker = Text.safe(
                System.getenv("CAUSYNTH_CONCOLIC_WORKER_DIR"));
        if (!worker.isEmpty()) {
            Path inWorker = readable(Paths.get(worker).resolve(name));
            if (inWorker != null) return inWorker;
        }
        String plan = Text.safe(System.getProperty(PLAN_PROPERTY));
        if (plan.isEmpty()) {
            plan = Text.safe(System.getenv("CAUSYNTH_CONCOLIC_TASK_PLAN"));
        }
        if (plan.isEmpty()) return null;
        Path beside = Paths.get(plan).getParent();
        return beside == null ? null : readable(beside.resolve(name));
    }

    private static Path readable(Path file) {
        return Files.isReadable(file) ? file : null;
    }

    /** Reads the focus row this replay was handed, once. */
    /** The versions the world of this replay chose, in the rows' order. */
    static List<ReadsFrom> versions() {
        load();
        synchronized (LOCK) {
            return new ArrayList<ReadsFrom>(VERSIONS);
        }
    }

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
            MINTED.clear();
            REACHED.clear();
            unmatchedPrefix = "";
            ROOT_MINTS.clear();
            task = null;
            OBLIGATIONS.clear();
            CLOCK_DELTAS.clear();
            VERSIONS.clear();
            FOCUS.clear();
            REFUSALS.clear();
            FLIPPED.clear();
            FOCUSED_TASKS.clear();
            FOCUSED_OCCURRENCES.clear();
            INHERITED.clear();
            INHERITED_OCCURRENCES.clear();
            SHORTFALLS.clear();
        }
    }
}
