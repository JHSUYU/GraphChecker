package edu.uva.liftlab.graphchecker.d3.explore;

import edu.uva.liftlab.graphchecker.d3.contract.Obligation;
import edu.uva.liftlab.graphchecker.d3.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.d3.contract.Task;
import edu.uva.liftlab.graphchecker.d3.contract.Verdict;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The per-task fixed point, and the wave that is the union of them.
 *
 * <p>Each task has its own frontier: the queries already answered, and the
 * flips still worth asking.  A wave is simply every task's open flips
 * together -- tasks do not wait for each other, and a result never reaches
 * across.</p>
 *
 * <p><b>Admission is per task.</b> {@link Verdict#NOT_ADMITTED} says the
 * FOCUSED occurrence's prefix did not match in that replay; it closes that
 * one query and nothing else.  A producer region that diverged in the same
 * replay is its own task's business: it has its own obligations, its own
 * admission and its own frontier.  This is what a linked replay could not do
 * -- one companion's mismatch rejected the primary -- and it is the reason a
 * result is keyed by obligation and never by replay.</p>
 *
 * <p>A {@link Verdict#ADMITTED} replay publishes a new session; that session
 * joins the corpus, and the new path it recorded yields new obligations with
 * new ids on the next wave.  That is how a nested guard chain deepens: wave
 * <i>n</i> flips {@code s1}, wave <i>n+1</i> finds {@code s2} on the path the
 * flip recorded, with the previous wave's answers inside its own prefix.  The
 * frontier is rebuilt from the recorded verdicts at the start of every wave,
 * so a wave never re-asks a query some earlier wave answered -- whatever the
 * answer was.</p>
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
    /** Every query some wave already answered. */
    private final Map<String, Verdict> answered =
            new LinkedHashMap<String, Verdict>();
    /** obligation id -> the task that proposed it, this wave. */
    private final Map<String, String> proposedBy =
            new LinkedHashMap<String, String>();
    private final List<String> validatedSessions = new ArrayList<String>();

    public Frontier(List<Task> tasks) {
        this.tasks = Collections.unmodifiableList(new ArrayList<Task>(tasks));
    }

    /**
     * Takes the verdicts the waves before this one recorded.
     *
     * <p>Every verdict closes its own query. An ADMITTED replay's session is
     * in the corpus by now, where the path it recorded is what the next
     * proposal is cut from; NOT_ADMITTED and DIVERGED are recorded and not
     * retried, the first saying this task's own prefix did not match, the
     * second that the replay left the epoch's topology -- neither a question
     * the same query can answer a second time.</p>
     */
    public void consume(Collection<ObligationResult> results) {
        for (ObligationResult result : results) {
            answered.put(result.obligationId(), result.verdict());
            if (result.verdict() == Verdict.ADMITTED
                    && !result.sessionId().isEmpty()
                    && !validatedSessions.contains(result.sessionId())) {
                validatedSessions.add(result.sessionId());
            }
        }
    }

    /** Whether some wave has already answered this query. */
    public boolean asked(String obligationId) {
        return answered.containsKey(obligationId);
    }

    /** Opens one wave over the flips the tasks still offer. */
    public Wave open(int index,
                     List<ObligationFactory.Candidate> candidates) {
        List<Obligation> obligations = new ArrayList<Obligation>();
        Set<String> proposed = new LinkedHashSet<String>();
        for (ObligationFactory.Candidate candidate : candidates) {
            if (answered.containsKey(candidate.obligationId)) continue;
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
