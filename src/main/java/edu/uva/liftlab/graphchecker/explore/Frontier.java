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

public final class Frontier {
    public static final class Round {
        public final int index;
        public final List<Obligation> obligations;
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
    private final Map<String, String> settled =
            new LinkedHashMap<String, String>();
    private final Map<String, Verdict> answered =
            new LinkedHashMap<String, Verdict>();
    private final Map<String, String> armRefusals =
            new LinkedHashMap<String, String>();
    private final Set<String> recorded = new LinkedHashSet<String>();
    private final Map<String, String> proposedBy =
            new LinkedHashMap<String, String>();
    private final Set<String> admittedFlips = new LinkedHashSet<String>();
    private final Set<String> worldOnlyFlips = new LinkedHashSet<String>();
    static final int MAX_BOUNDED_REPLAYS = 2;
    private final Set<String> boundedFlips = new LinkedHashSet<String>();
    private final Set<String> inFlightIds = new LinkedHashSet<String>();
    private final Set<String> inFlightFlips = new LinkedHashSet<String>();

    public Frontier(Corpus corpus, List<Task> tasks,
                    Map<String, Set<String>> flipSites) {
        this.tasks = Collections.unmodifiableList(new ArrayList<Task>(tasks));
        List<ObligationFactory.Keyed> arms =
                new ArrayList<ObligationFactory.Keyed>();
        for (Task task : this.tasks) {
            Set<String> sites = flipSites.get(task.taskId());
            if (sites == null) continue;
            for (Corpus.RecordedPath path : corpus.pathsOf(task.focused())) {
                for (int index = 0; index < path.decisions.size(); index++) {
                    DecisionRow decision = path.decisions.get(index);
                    if (FlipQuery.asks(sites, decision)
                            && FlipQuery.flippable(decision)) {
                        arms.add(new ObligationFactory.Keyed(task, path,
                                index));
                    }
                }
            }
        }
        List<String> dependences = ObligationFactory.dependences(corpus,
                arms);
        for (int at = 0; at < arms.size(); at++) {
            ObligationFactory.Keyed keyed = arms.get(at);
            DecisionRow decision = keyed.path.decisions.get(keyed.index);
            String arm = ObligationFactory.obligationId(
                    keyed.task.taskId(), decision.siteId(),
                    decision.ordinal(), decision.outcome(),
                    dependences.get(at));
            recorded.add(arm);
            settle(arm,
                    "arm already recorded by " + keyed.path.sessionId
                            + ": this occurrence took that arm at "
                            + "that site under what its guard "
                            + "depends on, so a focused replay of it "
                            + "would collect nothing the corpus "
                            + "lacks (PIPELINE §7: exploration "
                            + "collects the arms the seed LACKS)");
        }
    }

    public void consume(Collection<ObligationResult> results,
                        Map<String, List<ObligationResult>> byFlip) {
        for (Map.Entry<String, List<ObligationResult>> flip
                : byFlip.entrySet()) {
            int worldOnly = 0;
            int bounded = 0;
            boolean answeredArm = false;
            for (ObligationResult result : flip.getValue()) {
                if (result.verdict() == Verdict.ADMITTED) {
                    admittedFlips.add(flip.getKey());
                }
                if (result.replayBounded()) {
                    bounded++;
                } else if (result.verdict() == Verdict.NOT_ADMITTED
                        && result.refutation() == null
                        && !result.settlesArm()) {
                    worldOnly++;
                }
                answeredArm |= result.settlesArm();
            }
            if (worldOnly >= 2) {
                worldOnlyFlips.add(flip.getKey());
            } else if (bounded >= MAX_BOUNDED_REPLAYS && !answeredArm) {
                boundedFlips.add(flip.getKey());
            }
        }
        for (ObligationResult result : results) {
            answered.put(result.obligationId(), result.verdict());
            if (!result.settlesArm()) continue;
            String refusal = result.armRefusal();
            if (refusal != null) {
                armRefusals.putIfAbsent(result.obligationId(), refusal);
            }
            settle(result.obligationId(), "arm already answered "
                    + result.verdict() + (refusal == null ? ""
                    : " (" + refusal + ")") + " by an earlier round"
                    + (result.sessionId().isEmpty() ? ""
                    : " (session " + result.sessionId() + ")")
                    + ": an arm is owed once per planned occurrence, and this "
                    + "one is a fact about the occurrence, not about the "
                    + "session whose path it was cut from");
        }
    }

    public void inFlight(Collection<Obligation> flying) {
        for (Obligation obligation : flying) {
            inFlightIds.add(obligation.obligationId());
            inFlightFlips.add(ObligationFactory.flip(obligation.taskId(),
                    obligation.pathId(), obligation.siteId(),
                    obligation.ordinal(), obligation.flippedOutcome()));
        }
    }

    public boolean flying(ObligationFactory.Candidate candidate) {
        return inFlightIds.contains(candidate.obligationId)
                || inFlightFlips.contains(ObligationFactory.flip(candidate));
    }

    public boolean flying(String flip) {
        return inFlightFlips.contains(flip);
    }

    public int inFlightCount() {
        return inFlightIds.size();
    }

    public Verdict verdict(String obligationId) {
        return answered.get(obligationId);
    }

    public String armRefusal(String obligationId) {
        return armRefusals.get(obligationId);
    }

    public boolean inFlight(String obligationId) {
        return inFlightIds.contains(obligationId);
    }

    public boolean recorded(String obligationId) {
        return recorded.contains(obligationId);
    }

    public String settled(String obligationId) {
        return settled.getOrDefault(obligationId, "");
    }

    public String settled(ObligationFactory.Candidate candidate) {
        String reason = settled(candidate.obligationId);
        if (!reason.isEmpty()) return reason;
        String flip = ObligationFactory.flip(candidate);
        if (admittedFlips.contains(flip)) {
            return "flip already ADMITTED by an earlier round under another "
                    + "dependence: a replay of this flip of this path took "
                    + "the arm in the path's world, and only the sessions "
                    + "landed since moved its key";
        }
        if (worldOnlyFlips.contains(flip)) {
            return "flip answered NOT_ADMITTED twice in its own world, whose "
                    + "replays did not run it: a fact about that world, so "
                    + "the arm stays owed in others";
        }
        return boundedFlips.contains(flip) ? "BOUNDED by replay_timeout_s: "
                + "the flip's replays were killed past their bound "
                + MAX_BOUNDED_REPLAYS + " times and answered nothing, so it "
                + "is held unproposed, open, never settled" : "";
    }

    public Set<String> boundedFlips() {
        return Collections.unmodifiableSet(boundedFlips);
    }

    private void settle(String obligationId, String reason) {
        settled.putIfAbsent(obligationId, reason);
    }

    public Round open(int index, Obligation first,
                      List<ObligationFactory.Candidate> candidates) {
        List<Obligation> obligations = new ArrayList<Obligation>();
        Set<String> proposed = new LinkedHashSet<String>();
        int held = 0;
        if (first != null && !settled.containsKey(first.obligationId())) {
            if (inFlightIds.contains(first.obligationId())) {
                held++;
            } else {
                proposed.add(first.obligationId());
                proposedBy.put(first.obligationId(), first.taskId());
                obligations.add(first);
            }
        }
        for (ObligationFactory.Candidate candidate : candidates) {
            if (!settled(candidate).isEmpty()) continue;
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

    public Map<String, Integer> proposedPerTask() {
        Map<String, Integer> counts = new LinkedHashMap<String, Integer>();
        for (Task task : tasks) counts.put(task.taskId(), 0);
        for (String taskId : proposedBy.values()) {
            counts.merge(taskId, 1, Integer::sum);
        }
        return counts;
    }

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
