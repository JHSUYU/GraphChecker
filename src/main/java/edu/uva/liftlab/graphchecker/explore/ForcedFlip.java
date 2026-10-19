package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

final class ForcedFlip {
    static final String FORCE = "FORCE";

    static final class Round {
        final Obligation force;
        final List<ObligationFactory.Candidate> candidates;
        final JsonObject manifest;

        private Round(Obligation force,
                      List<ObligationFactory.Candidate> candidates,
                      JsonObject manifest) {
            this.force = force;
            this.candidates = candidates;
            this.manifest = manifest;
        }
    }

    private ForcedFlip() {
    }

    static Obligation force(Corpus corpus, Task task) {
        return Obligation.forcing(ArtifactIO.digest("force|"
                        + task.taskId(), 16), task.taskId(),
                Corpus.pathId(corpus.seedSessionId(), task.focused()));
    }

    static String flip(Obligation force) {
        return ObligationFactory.flip(force.taskId(), force.pathId(),
                force.siteId(), force.ordinal(), force.flippedOutcome());
    }

    static Round plan(Corpus corpus, Task anchor, StaticScopeMap scope,
                      Frontier frontier, List<ObligationResult> results,
                      Map<String, List<ObligationResult>> answers,
                      List<ObligationFactory.Candidate> candidates) {
        JsonObject manifest = new JsonObject();
        Set<String> sites = scope.forcedSites();
        if (anchor == null || sites.isEmpty()) {
            manifest.addProperty("state", "NO_FORCING_TABLE");
            return new Round(null, candidates, manifest);
        }
        Obligation force = force(corpus, anchor);
        String forceFlip = flip(force);
        Verdict answered = answer(answers.get(forceFlip));
        boolean bounded = frontier.boundedFlips().contains(forceFlip);
        manifest.addProperty("obligationId", force.obligationId());
        manifest.addProperty("state", answered != null ? answered.name()
                : bounded ? "BOUNDED"
                : frontier.inFlight(force.obligationId()) ? "IN_FLIGHT"
                : "PROPOSED");
        for (ObligationResult result : results) {
            if (!result.obligationId().equals(force.obligationId())) continue;
            manifest.addProperty("detail", result.detail());
            manifest.addProperty("sessionId", result.sessionId());
        }
        List<ObligationFactory.Candidate> forced =
                ObligationFactory.forced(corpus, anchor);
        boolean flipAnswered = false;
        for (ObligationFactory.Candidate flip : forced) {
            Verdict verdict = answer(answers.get(ObligationFactory.flip(flip)));
            flipAnswered = flipAnswered || verdict != null;
            manifest.addProperty("forcedFlip", flip.obligationId);
            manifest.addProperty("forcedFlipVerdict", verdict != null
                    ? verdict.name() : frontier.flying(flip) ? "IN_FLIGHT"
                    : "OPEN");
        }
        manifest.addProperty("forcedPaths", forced.size());
        String seed = corpus.seedSessionId();
        List<ObligationFactory.Candidate> round =
                new ArrayList<ObligationFactory.Candidate>(forced);
        int after = 0;
        for (ObligationFactory.Candidate candidate : candidates) {
            if (flipAnswered && candidate.task.taskId().equals(
                    anchor.taskId()) && seed.equals(candidate.path.sessionId)
                    && sites.contains(candidate.siteId())
                    && frontier.settled(candidate).isEmpty()
                    && !frontier.flying(candidate)) {
                after++;
            }
            round.add(candidate);
        }
        manifest.addProperty("seedFlipsAfterForcedFlip", after);
        boolean forceOwed = answered == null && !bounded
                && !forcedSessionLanded(corpus, anchor.focused());
        return new Round(forceOwed ? force : null, round, manifest);
    }

    private static Verdict answer(List<ObligationResult> asked) {
        Verdict last = null;
        for (ObligationResult result : asked == null
                ? Collections.<ObligationResult>emptyList() : asked) {
            if (result.verdict() != Verdict.SAT_MODEL_READY
                    && result.refutation() == null
                    && !result.replayBounded()) {
                last = result.verdict();
            }
        }
        return last;
    }

    private static boolean forcedSessionLanded(Corpus corpus,
                                               OccurrenceAddress anchor) {
        return !corpus.forcedPaths(anchor).isEmpty();
    }
}
