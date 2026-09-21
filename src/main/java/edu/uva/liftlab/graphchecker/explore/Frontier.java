package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.Verdict;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The one ledger of owed arms, and the wave that is what is still owed.
 *
 * <p><b>An arm is a fact about a PLANNED OCCURRENCE ON ONE PREFIX, not about
 * a session.</b>
 * Its key is {@link ObligationFactory#obligationId} -- the task (which is the
 * occurrence, {@link ClosurePlanner#taskId}), the site, the ordinal, the
 * flipped outcome, the digest of the prefix the flip is cut under
 * ({@link ObligationFactory#prefixDigest}) and the digest of the WORLD it is
 * cut in ({@link ObligationFactory#worldDigest}) -- and it is owed ONCE
 * across the whole corpus.  It stops being owed when either of two things is
 * true, and this class is the one place that holds both:</p>
 *
 * <ul>
 *   <li><b>some session recorded it, on that prefix.</b> A
 *       {@link DecisionRow} of that occurrence at that site and ordinal with
 *       that outcome, under the same prefix, in ANY session of the epoch
 *       ({@link Corpus#pathsOf} spans them) -- because an arm is attested by
 *       the identity that took it, not by the session that holds the row.
 *       The PREFIX and the WORLD are part of the key: an unexplored local
 *       path of a known region is still work, and so is a known local path
 *       in a world that changed what the region received -- never the same
 *       path in a world that changed nothing for it.  A wave that adds no
 *       new edge to the region graph is not the end of the exploration.
 *       HDFS-11741 is why: its witness needs dn1's expiry compare flipped
 *       again in the world where nn0's second rotation dropped the key, and
 *       dn1's own prefix there is letter for letter the seed's -- the scan
 *       runs over the DataNode's old map before the put loop -- so keyed by
 *       the prefix alone that obligation is settled by the session that took
 *       the arm in another world, and the two flips are never joined.  The
 *       world is asked only where it AFFECTED the region
 *       ({@link Corpus#affected}: the occurrence's own rows or those of any
 *       state-connected member of its factor), or every session of the epoch
 *       would re-ask every arm it holds -- and what is then asked is the
 *       part of that world which REACHES the task
 *       ({@link ObligationFactory#worldKey}, over
 *       {@link Corpus#upstreamOf}), or every combination of flips
 *       elsewhere in the topology would re-ask it just as often.</li>
 *   <li><b>a wave answered it.</b> ADMITTED, UNSAT or NOT_ADMITTED in
 *       {@code obligation_results.jsonl}.  Every verdict closes its own arm:
 *       an ADMITTED replay's session is in the corpus by now, and
 *       NOT_ADMITTED says this task's own prefix did not match -- not a
 *       question the same query can answer a second time.  A
 *       {@link Verdict#SAT_MODEL_READY} row is NOT an answer: it says the
 *       query was solved and the replay has not run, so the arm is still
 *       owed.</li>
 * </ul>
 *
 * <p>The two used to be two ledgers keyed differently -- this class held the
 * answered ids and {@code ObligationFactory} held the recorded arms -- and
 * the answered id carried the {@code pathId}, so it was a fact about a
 * SESSION.  Every session mints its own {@code pathId}
 * ({@link Corpus#pathId}), so an arm answered out of the seed was re-proposed
 * out of every replay the answer produced: on the 11741 campaign #2 corpus
 * (81 sessions) wave 0 answered 36 arms of which 30 left no recorded
 * DecisionRow behind, and wave 1 re-proposed exactly those 30 as 706
 * obligations -- 30 facts asked 706 times, at ~300s of focused replay each.
 * A new obligation arises only for a NEW planned occurrence (closure growth)
 * or a guard no session has taken both ways.</p>
 *
 * <p><b>Admission is per task.</b> {@link Verdict#NOT_ADMITTED} says the
 * FOCUSED occurrence's prefix did not match in that replay; it closes that
 * one arm and nothing else.  A producer region that diverged in the same
 * replay is its own task's business: it has its own obligations, its own
 * admission and its own frontier.  This is what a linked replay could not do
 * -- one companion's mismatch rejected the primary -- and it is the reason a
 * result is keyed by obligation and never by replay.</p>
 *
 * <p>That is how a nested guard chain deepens: wave <i>n</i> flips {@code s1},
 * wave <i>n+1</i> finds {@code s2} on the path the flip recorded, with the
 * previous wave's answers inside its own prefix.  The ledger is rebuilt from
 * the corpus and the recorded verdicts at the start of every wave, so a wave
 * never re-asks an arm that is settled -- however it was settled.</p>
 */
public final class Frontier {
    /** One wave: the flips the runtime is asked to solve and replay. */
    public static final class Wave {
        public final int index;
        public final List<Obligation> obligations;

        private Wave(int index, List<Obligation> obligations) {
            this.index = index;
            this.obligations = Collections.unmodifiableList(obligations);
        }

        public boolean empty() {
            return obligations.isEmpty();
        }
    }

    private final List<Task> tasks;
    /** arm key -> what settled it, in the words a gap row prints. */
    private final Map<String, String> settled =
            new LinkedHashMap<String, String>();
    /** The arms a wave answered, for the manifest's histogram. */
    private final Map<String, Verdict> answered =
            new LinkedHashMap<String, Verdict>();
    /** arm key -> the task that proposed it, this wave. */
    private final Map<String, String> proposedBy =
            new LinkedHashMap<String, String>();

    /**
     * Indexes every arm the CORPUS has already recorded for these tasks.
     *
     * <p>Unbounded over paths on purpose: {@code maxPathsPerTask} bounds what
     * a wave may cut a flip FROM, and a path past that bound still attests
     * the arms it took.  On the 11741 corpus that is 81 sessions attesting
     * against a flip budget of 32.</p>
     */
    public Frontier(Corpus corpus, List<Task> tasks) {
        this.tasks = Collections.unmodifiableList(new ArrayList<Task>(tasks));
        for (Task task : this.tasks) {
            for (Corpus.RecordedPath path : corpus.pathsOf(task.focused())) {
                // AND IN THE WORLD IT WAS TAKEN IN, where that world reached
                // the region at all: a recording in a session whose world
                // changed nothing for this occurrence or its factor settles
                // the world-less arm -- the one every other such session
                // offers -- and a recording in a session whose world DID
                // change what the region received settles only its own
                // world's arm, that world being the flips of it that REACH
                // this task (ObligationFactory.worldKey).  The candidate a
                // wave cuts is keyed by the same call, because a ledger and
                // a proposal that key one arm differently never meet.
                String world = ObligationFactory.worldKey(corpus, task,
                        path.sessionId);
                for (int index = 0; index < path.decisions.size(); index++) {
                    DecisionRow decision = path.decisions.get(index);
                    // UNDER THE PREFIX IT WAS TAKEN ON: the same arm on
                    // another prefix of the same occurrence is another
                    // obligation, and this one settles nothing about it.
                    settle(ObligationFactory.obligationId(task.taskId(),
                                    decision.siteId(), decision.ordinal(),
                                    decision.outcome(),
                                    ObligationFactory.prefixDigest(
                                            path.decisions, index),
                                    world),
                            "arm already recorded by " + path.sessionId
                                    + ": this occurrence took that arm at "
                                    + "that site on that prefix in that "
                                    + "session, so a "
                                    + "focused replay of it would collect "
                                    + "nothing the corpus lacks (HANDOVER "
                                    + "SS1.5: exploration collects the arms "
                                    + "the seed LACKS)");
                }
            }
        }
    }

    /**
     * Takes the verdicts the waves before this one recorded.
     *
     * <p>A recording outranks a verdict as the reason: both settle the arm,
     * and "some session took it" is the stronger thing to say about one.</p>
     */
    public void consume(Collection<ObligationResult> results) {
        for (ObligationResult result : results) {
            answered.put(result.obligationId(), result.verdict());
            if (result.verdict() == Verdict.SAT_MODEL_READY) continue;
            settle(result.obligationId(), "arm already answered "
                    + result.verdict() + " by an earlier wave"
                    + (result.sessionId().isEmpty() ? ""
                    : " (session " + result.sessionId() + ")")
                    + ": an arm is owed once per planned occurrence, and this "
                    + "one is a fact about the occurrence, not about the "
                    + "session whose path it was cut from");
        }
    }

    /** The first reason this arm is settled, or {@code ""} while it is owed. */
    public String settled(String obligationId) {
        String reason = settled.get(obligationId);
        return reason == null ? "" : reason;
    }

    private void settle(String obligationId, String reason) {
        if (!settled.containsKey(obligationId)) {
            settled.put(obligationId, reason);
        }
    }

    /** Opens one wave over the arms the tasks still owe. */
    public Wave open(int index,
                     List<ObligationFactory.Candidate> candidates) {
        List<Obligation> obligations = new ArrayList<Obligation>();
        Set<String> proposed = new LinkedHashSet<String>();
        for (ObligationFactory.Candidate candidate : candidates) {
            if (settled.containsKey(candidate.obligationId)) continue;
            if (!proposed.add(candidate.obligationId)) continue;
            proposedBy.put(candidate.obligationId,
                    candidate.task.taskId());
            obligations.add(candidate.proposal());
        }
        return new Wave(index, obligations);
    }

    /** Per task: how many queries are answered, and how many this wave asks. */
    public Map<String, int[]> perTask() {
        Map<String, int[]> counts = new LinkedHashMap<String, int[]>();
        for (Task task : tasks) counts.put(task.taskId(), new int[]{0, 0});
        for (Map.Entry<String, String> entry : proposedBy.entrySet()) {
            int[] count = counts.get(entry.getValue());
            if (count == null) {
                count = new int[]{0, 0};
                counts.put(entry.getValue(), count);
            }
            count[1]++;
        }
        return counts;
    }

    /** How many queries ended in each verdict, over every wave so far. */
    public Map<String, Integer> verdictHistogram() {
        Map<String, Integer> histogram = new LinkedHashMap<String, Integer>();
        for (Verdict verdict : answered.values()) {
            Integer count = histogram.get(verdict.name());
            histogram.put(verdict.name(), count == null ? 1 : count + 1);
        }
        return histogram;
    }

    public int answeredCount() {
        return answered.size();
    }
}
