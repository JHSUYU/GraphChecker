package edu.uva.liftlab.graphchecker.d3.explore;

import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
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
 * <p>Each task has its own frontier: the obligations it has issued and is
 * waiting for, the ones it has closed, and the queries it will not ask
 * again.  A wave is simply every task's pending obligations together --
 * tasks do not wait for each other, and a result never reaches across.</p>
 *
 * <p><b>Admission is per task.</b> {@link Verdict#NOT_ADMITTED} says the
 * FOCUSED occurrence's prefix did not match in that replay; it closes that
 * one query and nothing else.  A producer region that diverged in the same
 * replay is its own task's business: it has its own obligations, its own
 * admission and its own frontier.  This is what a linked replay could not do
 * -- one companion's mismatch rejected the primary -- and it is the reason a
 * result is keyed by obligation and never by replay.</p>
 *
 * <p>A {@link Verdict#VALIDATED} replay publishes a new session; that session
 * joins the corpus, and the new path it recorded yields new obligations with
 * new ids on the next wave.  That is how a nested guard chain deepens: wave
 * <i>n</i> flips {@code s1}, wave <i>n+1</i> finds {@code s2} on the path the
 * flip recorded, with the previous wave's answers inside its own prefix.  The
 * loop stops when no task has a pending obligation and no new one is offered,
 * or at the wave budget -- never because "the obligation I planned is
 * done".</p>
 */
public final class Frontier {
    /** One wave: what the runtime is asked to run, and what closed here. */
    public static final class Wave {
        public final int index;
        public final List<Obligation> obligations;
        public final List<ObligationResult> closed;
        public final List<GapRow> gaps;

        private Wave(int index, List<Obligation> obligations,
                     List<ObligationResult> closed, List<GapRow> gaps) {
            this.index = index;
            this.obligations = Collections.unmodifiableList(obligations);
            this.closed = Collections.unmodifiableList(closed);
            this.gaps = Collections.unmodifiableList(gaps);
        }

        public boolean empty() {
            return obligations.isEmpty() && closed.isEmpty();
        }
    }

    private final List<Task> tasks;
    /** obligation id -> the task that issued it. */
    private final Map<String, String> issuedBy =
            new LinkedHashMap<String, String>();
    private final Map<String, Obligation> pending =
            new LinkedHashMap<String, Obligation>();
    /** Every query already asked: closed, refused, or answered. */
    private final Set<String> asked = new LinkedHashSet<String>();
    private final Map<String, Verdict> verdicts =
            new LinkedHashMap<String, Verdict>();
    private final List<String> validatedSessions = new ArrayList<String>();

    public Frontier(List<Task> tasks) {
        this.tasks = Collections.unmodifiableList(new ArrayList<Task>(tasks));
    }

    public List<Task> tasks() {
        return tasks;
    }

    /** Whether this query has been asked before, in any wave. */
    public boolean asked(String obligationId) {
        return asked.contains(obligationId);
    }

    /**
     * Opens one wave from the obligations the factory offers.
     *
     * <p>An outcome whose query was refused, or which the solver closed
     * UNSAT, is recorded and never issued: a wave costs a replay only for a
     * flip some world of the corpus supports.</p>
     */
    public Wave open(int index, List<ObligationFactory.Outcome> outcomes) {
        List<Obligation> issue = new ArrayList<Obligation>();
        List<ObligationResult> closed = new ArrayList<ObligationResult>();
        List<GapRow> gaps = new ArrayList<GapRow>();
        for (ObligationFactory.Outcome outcome : outcomes) {
            if (asked.contains(outcome.obligationId)) continue;
            gaps.addAll(outcome.gaps);
            asked.add(outcome.obligationId);
            issuedBy.put(outcome.obligationId, outcome.taskId);
            if (outcome.issued()) {
                pending.put(outcome.obligationId, outcome.obligation);
                issue.add(outcome.obligation);
            } else if (outcome.result != null) {
                closed.add(outcome.result);
                verdicts.put(outcome.obligationId, outcome.result.verdict());
            }
        }
        return new Wave(index, issue, closed, gaps);
    }

    /** Replays the state of a wave this run did not plan itself. */
    public void restore(Collection<Obligation> obligations,
                        Collection<ObligationResult> results) {
        for (Obligation obligation : obligations) {
            asked.add(obligation.obligationId());
            issuedBy.put(obligation.obligationId(), obligation.taskId());
            pending.put(obligation.obligationId(), obligation);
        }
        consume(results);
    }

    /**
     * Takes the runtime's verdicts.
     *
     * <p>Every verdict closes its own query -- the same obligation is never
     * issued again, because the answer would be the same.  A VALIDATED replay
     * adds its session to the corpus, where the path it recorded becomes the
     * next wave's obligations.  NOT_ADMITTED and DIVERGED are recorded and
     * not retried: the first says this task's own prefix did not match, the
     * second that the replay left the epoch's topology, and neither is a
     * question the same query can answer a second time.</p>
     */
    public void consume(Collection<ObligationResult> results) {
        for (ObligationResult result : results) {
            asked.add(result.obligationId());
            pending.remove(result.obligationId());
            verdicts.put(result.obligationId(), result.verdict());
            if (result.verdict() == Verdict.VALIDATED
                    && !result.sessionId().isEmpty()
                    && !validatedSessions.contains(result.sessionId())) {
                validatedSessions.add(result.sessionId());
            }
        }
    }

    public boolean hasPending() {
        return !pending.isEmpty();
    }

    public List<Obligation> pending() {
        return new ArrayList<Obligation>(pending.values());
    }

    public List<String> validatedSessions() {
        return Collections.unmodifiableList(validatedSessions);
    }

    /** Per task: how many queries were asked, and how many are still open. */
    public Map<String, int[]> perTask() {
        Map<String, int[]> counts = new LinkedHashMap<String, int[]>();
        for (Task task : tasks) counts.put(task.taskId(), new int[]{0, 0});
        for (Map.Entry<String, String> entry : issuedBy.entrySet()) {
            int[] count = counts.get(entry.getValue());
            if (count == null) {
                count = new int[]{0, 0};
                counts.put(entry.getValue(), count);
            }
            count[0]++;
            if (pending.containsKey(entry.getKey())) count[1]++;
        }
        return counts;
    }

    /** How many queries ended in each verdict. */
    public Map<String, Integer> verdictHistogram() {
        Map<String, Integer> histogram = new LinkedHashMap<String, Integer>();
        for (Verdict verdict : verdicts.values()) {
            Integer count = histogram.get(verdict.name());
            histogram.put(verdict.name(), count == null ? 1 : count + 1);
        }
        return histogram;
    }
}
