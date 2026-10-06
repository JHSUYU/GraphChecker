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
 * The one ledger of owed arms; a round is what is still owed.
 *
 * <p><b>An arm is a fact about a PLANNED OCCURRENCE under what its guard
 * depends on, never about a session.</b> Its key is {@link
 * ObligationFactory#obligationId}: task ({@link ClosurePlanner#taskId}), site,
 * ordinal, flipped outcome and {@link ObligationFactory#dependence} (the path
 * condition and the world the guard rests on). It is owed once across the
 * corpus and settled when either:</p>
 *
 * <ul>
 *   <li><b>some session recorded it</b> under the same dependence ({@link
 *       Corpus#pathsOf} spans sessions). Trap: keying by the path condition
 *       alone lets a recording over other inputs settle an arm that is still
 *       needed (hdfs-11741: the same expiry compare over a map of four keys
 *       instead of five).</li>
 *   <li><b>a round answered it</b>: ADMITTED, UNSAT or NOT_ADMITTED.
 *       {@link Verdict#SAT_MODEL_READY} is NOT an answer (replay not
 *       run).</li>
 * </ul>
 *
 * <p>An arm queued or running ({@link #inFlight}) is not settled and not
 * proposed again: by its id, and by the flip its row asks ({@link
 * ObligationFactory#flip}), since its id may move while it is in flight:
 * sessions landing since its round grow the dependence.</p>
 *
 * <p>Trap: keying by session ({@code pathId}) re-proposes every answered arm
 * from every replay it produced. New obligations arise only from new planned
 * occurrences or guards no session has taken both ways.</p>
 *
 * <p><b>Admission is per task:</b> NOT_ADMITTED closes the focused arm only; a
 * diverging producer is its own task's business. Results are keyed by
 * obligation, never by replay. The ledger is rebuilt each round, so nested
 * guard chains deepen without re-asking settled arms.</p>
 */
public final class Frontier {
    /** One round: the flips the runtime is asked to solve and replay. */
    public static final class Round {
        public final int index;
        public final List<Obligation> obligations;
        /** Candidates not proposed because they are in flight. */
        public final int heldInFlight;

        private Round(int index, List<Obligation> obligations,
                      int heldInFlight) {
            this.index = index;
            this.obligations = Collections.unmodifiableList(obligations);
            this.heldInFlight = heldInFlight;
        }

        public boolean empty() {
            return obligations.isEmpty();
        }
    }

    private final List<Task> tasks;
    /** arm key -> the reason it is settled, as a gap row prints it. */
    private final Map<String, String> settled =
            new LinkedHashMap<String, String>();
    /** Arms a round answered, for the manifest histogram. */
    private final Map<String, Verdict> answered =
            new LinkedHashMap<String, Verdict>();
    /** Arms a recorded path already took. */
    private final Set<String> recorded = new LinkedHashSet<String>();
    /** arm key -> proposing task, this round. */
    private final Map<String, String> proposedBy =
            new LinkedHashMap<String, String>();
    /** The ids, and the flips, of the arms queued or running. */
    private final Set<String> inFlightIds = new LinkedHashSet<String>();
    private final Set<String> inFlightFlips = new LinkedHashSet<String>();

    /** Indexes every arm the corpus recorded for these tasks, over all paths:
     *  {@code maxPathsPerTask} bounds what a flip is cut from, not what
     *  attests. Only at the task's flip sites ({@link
     *  ObligationFactory#candidates}): no candidate is keyed anywhere else.
     *
     *  @param flipSites task id -> the site ids its demand names */
    public Frontier(Corpus corpus, List<Task> tasks,
                    Map<String, Set<String>> flipSites) {
        this.tasks = Collections.unmodifiableList(new ArrayList<Task>(tasks));
        for (Task task : this.tasks) {
            Set<String> sites = flipSites.get(task.taskId());
            if (sites == null) continue;
            for (Corpus.RecordedPath path : corpus.pathsOf(task.focused())) {
                for (int index = 0; index < path.decisions.size(); index++) {
                    DecisionRow decision = path.decisions.get(index);
                    if (!FlipQuery.asks(sites, decision)
                            || !FlipQuery.flippable(decision)) {
                        continue;
                    }
                    String arm = ObligationFactory.obligationId(
                            task.taskId(), decision.siteId(),
                            decision.ordinal(), decision.outcome(),
                            ObligationFactory.dependence(corpus, task, path,
                                    index));
                    recorded.add(arm);
                    settle(arm,
                            "arm already recorded by " + path.sessionId
                                    + ": this occurrence took that arm at "
                                    + "that site under what its guard "
                                    + "depends on, so a focused replay of it "
                                    + "would collect nothing the corpus "
                                    + "lacks (PIPELINE §7: exploration "
                                    + "collects the arms the seed LACKS)");
                }
            }
        }
    }

    /** Takes earlier rounds' verdicts; a recording, if any, stays the stated
     *  reason. */
    public void consume(Collection<ObligationResult> results) {
        for (ObligationResult result : results) {
            answered.put(result.obligationId(), result.verdict());
            if (result.verdict() == Verdict.SAT_MODEL_READY) continue;
            settle(result.obligationId(), "arm already answered "
                    + result.verdict() + " by an earlier round"
                    + (result.sessionId().isEmpty() ? ""
                    : " (session " + result.sessionId() + ")")
                    + ": an arm is owed once per planned occurrence, and this "
                    + "one is a fact about the occurrence, not about the "
                    + "session whose path it was cut from");
        }
    }

    /** Takes the arms a campaign has queued or started and not yet
     *  answered: none is proposed again while it is. */
    public void inFlight(Collection<Obligation> flying) {
        for (Obligation obligation : flying) {
            inFlightIds.add(obligation.obligationId());
            inFlightFlips.add(ObligationFactory.flip(obligation.taskId(),
                    obligation.pathId(), obligation.siteId(),
                    obligation.ordinal(), obligation.flippedOutcome()));
        }
    }

    /** Whether this candidate's arm is queued or running: by its id, or
     *  by its flip, since its id may move while it flies. */
    public boolean flying(ObligationFactory.Candidate candidate) {
        return inFlightIds.contains(candidate.obligationId)
                || inFlightFlips.contains(ObligationFactory.flip(candidate));
    }

    /** How many arms are queued or running. */
    public int inFlightCount() {
        return inFlightIds.size();
    }

    /** What a round answered for this arm, or null. */
    public Verdict verdict(String obligationId) {
        return answered.get(obligationId);
    }

    /** Whether a recorded path already took this arm. */
    public boolean recorded(String obligationId) {
        return recorded.contains(obligationId);
    }

    /** Whether this arm is queued or running. */
    public boolean inFlight(String obligationId) {
        return inFlightIds.contains(obligationId);
    }

    /** The first reason this arm is settled, or {@code ""} while it is owed. */
    public String settled(String obligationId) {
        return settled.getOrDefault(obligationId, "");
    }

    private void settle(String obligationId, String reason) {
        settled.putIfAbsent(obligationId, reason);
    }

    /** Opens one round over the arms the tasks still owe and nobody is
     *  asking yet. */
    public Round open(int index,
                      List<ObligationFactory.Candidate> candidates) {
        List<Obligation> obligations = new ArrayList<Obligation>();
        Set<String> proposed = new LinkedHashSet<String>();
        int held = 0;
        for (ObligationFactory.Candidate candidate : candidates) {
            if (settled.containsKey(candidate.obligationId)) continue;
            if (flying(candidate)) {
                held++;
                continue;
            }
            if (!proposed.add(candidate.obligationId)) continue;
            proposedBy.put(candidate.obligationId,
                    candidate.task.taskId());
            obligations.add(candidate.proposal());
        }
        return new Round(index, obligations, held);
    }

    /** Per task: how many obligations this round proposes. */
    public Map<String, Integer> proposedPerTask() {
        Map<String, Integer> counts = new LinkedHashMap<String, Integer>();
        for (Task task : tasks) counts.put(task.taskId(), 0);
        for (String taskId : proposedBy.values()) {
            counts.merge(taskId, 1, Integer::sum);
        }
        return counts;
    }

    /** How many queries ended in each verdict, over every round so far. */
    public Map<String, Integer> verdictHistogram() {
        Map<String, Integer> histogram = new LinkedHashMap<String, Integer>();
        for (Verdict verdict : answered.values()) {
            histogram.merge(verdict.name(), 1, Integer::sum);
        }
        return histogram;
    }

    public int answeredCount() {
        return answered.size();
    }

}
