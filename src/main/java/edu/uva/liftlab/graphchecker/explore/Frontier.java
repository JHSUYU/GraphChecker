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
 * The one ledger of owed arms; a wave is what is still owed.
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
 *   <li><b>a wave answered it</b>: ADMITTED, UNSAT or NOT_ADMITTED. {@link
 *       Verdict#SAT_MODEL_READY} is NOT an answer (replay not run).</li>
 *   <li><b>a wave answered its question</b> ({@link
 *       ObligationFactory#question}: the query as asked and the world it
 *       plants) under another id: an id drifts as sessions land, and one
 *       question gets one answer.</li>
 * </ul>
 *
 * <p>Trap: keying by session ({@code pathId}) re-proposes every answered arm
 * from every replay it produced. New obligations arise only from new planned
 * occurrences or guards no session has taken both ways.</p>
 *
 * <p><b>Admission is per task:</b> NOT_ADMITTED closes the focused arm only; a
 * diverging producer is its own task's business. Results are keyed by
 * obligation, never by replay. The ledger is rebuilt each wave, so nested guard
 * chains deepen without re-asking settled arms.</p>
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
    /** arm key -> the reason it is settled, as a gap row prints it. */
    private final Map<String, String> settled =
            new LinkedHashMap<String, String>();
    /** Arms a wave answered, for the manifest histogram. */
    private final Map<String, Verdict> answered =
            new LinkedHashMap<String, Verdict>();
    /** arm key -> proposing task, this wave. */
    private final Map<String, String> proposedBy =
            new LinkedHashMap<String, String>();
    /** question -> the reason it is answered, as a gap row prints it. */
    private final Map<String, String> askedBefore =
            new LinkedHashMap<String, String>();
    /** The flips those questions are about ({@code ObligationFactory#flip}). */
    private final Set<String> answeredFlips = new LinkedHashSet<String>();
    /** obligation id -> its question, for what this wave proposes. */
    private final Map<String, String> questions =
            new LinkedHashMap<String, String>();

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
                    if (!sites.contains(decision.siteId())
                            || !FlipQuery.flippable(decision)) {
                        continue;
                    }
                    settle(ObligationFactory.obligationId(task.taskId(),
                                    decision.siteId(), decision.ordinal(),
                                    decision.outcome(),
                                    ObligationFactory.dependence(corpus,
                                            task, path, index)),
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

    /** Takes earlier waves' verdicts, and the questions their solvers
     *  asked (obligation id -> question, {@code ObligationDir#questions});
     *  a recording, if any, stays the stated reason. */
    public void consume(Collection<ObligationResult> results,
                        Map<String, String> asked) {
        for (ObligationResult result : results) {
            answered.put(result.obligationId(), result.verdict());
            if (result.verdict() == Verdict.SAT_MODEL_READY) continue;
            String session = result.sessionId().isEmpty() ? ""
                    : " (session " + result.sessionId() + ")";
            settle(result.obligationId(), "arm already answered "
                    + result.verdict() + " by an earlier wave" + session
                    + ": an arm is owed once per planned occurrence, and this "
                    + "one is a fact about the occurrence, not about the "
                    + "session whose path it was cut from");
            String question = asked.getOrDefault(result.obligationId(), "");
            int split = question.indexOf(':');
            if (split < 0) continue;
            answeredFlips.add(question.substring(0, split));
            askedBefore.putIfAbsent(question, "question " + question
                    + " already answered " + result.verdict() + " by an "
                    + "earlier wave, as obligation " + result.obligationId()
                    + session + ": the same query in the same world gets "
                    + "the same answer");
        }
    }

    /** Why this question needs no asking, or {@code ""} while it does. */
    public String asked(String question) {
        return askedBefore.getOrDefault(question, "");
    }

    /** Whether an earlier wave answered a question about this flip. */
    public boolean answered(String flip) {
        return answeredFlips.contains(flip);
    }

    /** The first reason this arm is settled, or {@code ""} while it is owed. */
    public String settled(String obligationId) {
        return settled.getOrDefault(obligationId, "");
    }

    private void settle(String obligationId, String reason) {
        settled.putIfAbsent(obligationId, reason);
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
            questions.put(candidate.obligationId, candidate.question);
            obligations.add(candidate.proposal());
        }
        return new Wave(index, obligations);
    }

    /** Obligation id -> the question it asks (its flip, where no earlier
     *  wave answered one about it), for this wave's proposals. */
    public Map<String, String> questions() {
        return Collections.unmodifiableMap(questions);
    }

    /** Per task: how many obligations this wave proposes. */
    public Map<String, Integer> proposedPerTask() {
        Map<String, Integer> counts = new LinkedHashMap<String, Integer>();
        for (Task task : tasks) counts.put(task.taskId(), 0);
        for (String taskId : proposedBy.values()) {
            counts.merge(taskId, 1, Integer::sum);
        }
        return counts;
    }

    /** How many queries ended in each verdict, over every wave so far. */
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

    /** How many distinct questions earlier waves answered. */
    public int answeredQuestions() {
        return askedBefore.size();
    }
}
