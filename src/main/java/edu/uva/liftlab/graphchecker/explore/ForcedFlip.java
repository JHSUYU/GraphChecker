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

/**
 * EXPLORE's half of the forced replay (PIPELINE §7.10).  Every campaign's
 * first round asks ONE FORCE run of the declared anchor's task, queued
 * first: the recording's world with the anchor's branches forced to the
 * throw ({@code runtime.ForcedArms}).  Its forced session lands held apart
 * ({@code Corpus#forcedPaths}) and parents one forced flip ({@link
 * ObligationFactory#forced}), the anchor's whole fatal condition asked at
 * once, queued ahead of the round's other flips.  No other flip waits for
 * either: the seed path's flips at the forcing table's sites go out as they
 * would without them (solr-18413 FA4: holding its expiry flip behind the
 * FORCE run and the forced flip, two replays in a row, brought its witness
 * 590 s after round 0 instead of 251 s).
 */
final class ForcedFlip {
    /** How a FORCE worker's verdict detail opens. */
    static final String FORCE = "FORCE";

    /** One round's forced share. */
    static final class Round {
        /** The FORCE obligation while it is owed, else null. */
        final Obligation force;
        /** The candidates, the forced flips first. */
        final List<ObligationFactory.Candidate> candidates;
        /** The round manifest's {@code force} row. */
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

    /** The FORCE obligation of the anchor's task, cut from the seed. */
    static Obligation force(Corpus corpus, Task task) {
        return Obligation.forcing(ArtifactIO.digest("force|"
                        + task.taskId(), 16), task.taskId(),
                Corpus.pathId(corpus.seedSessionId(), task.focused()));
    }

    /**
     * The round's forced share for the anchor's task ({@code anchor} null:
     * none planned; a map with no forcing table: none): the FORCE
     * obligation while no round answered it and none flies, and the forced
     * flips ahead of {@code candidates}.  A forced flip's verdict is read by
     * the flip it asks ({@code answers}, {@link ExploreMain#answersByFlip}):
     * its id moves as sessions land, its flip does not.
     */
    static Round plan(Corpus corpus, Task anchor, StaticScopeMap scope,
                      Frontier frontier, List<ObligationResult> results,
                      Map<String, List<ObligationResult>> answers,
                      List<ObligationFactory.Candidate> candidates) {
        JsonObject manifest = new JsonObject();
        Set<String> sites = scope.forcedSites();
        if (anchor == null || sites.isEmpty()) {
            // No table, nothing to force: the seed's way stands alone.
            manifest.addProperty("state", "NO_FORCING_TABLE");
            return new Round(null, candidates, manifest);
        }
        Obligation force = force(corpus, anchor);
        Verdict answered = frontier.verdict(force.obligationId());
        manifest.addProperty("obligationId", force.obligationId());
        manifest.addProperty("state", answered == null
                ? frontier.inFlight(force.obligationId()) ? "IN_FLIGHT"
                : "PROPOSED" : answered.name());
        // What the forced world came to: its target reached forced (how
        // the occurrence then ended), or FORCE_DIVERGED and where.
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
            // Asked after the forced flip was answered: what the follow-up
            // deletion is decided on (PIPELINE §7.10).
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
        boolean forceOwed = (answered == null
                || answered == Verdict.SAT_MODEL_READY)
                && !forcedSessionLanded(corpus, anchor.focused());
        return new Round(forceOwed ? force : null, round, manifest);
    }

    /** The last verdict of a flip that answers it (not a solve whose
     *  replay is owed, nor a replay that refuted its world), or null. */
    private static Verdict answer(List<ObligationResult> asked) {
        Verdict last = null;
        for (ObligationResult result : asked == null
                ? Collections.<ObligationResult>emptyList() : asked) {
            if (result.verdict() != Verdict.SAT_MODEL_READY
                    && result.refutation() == null) {
                last = result.verdict();
            }
        }
        return last;
    }

    /** Whether a forced session of this occurrence is in the corpus: its
     *  FORCE run was answered, whatever the ledger reads. */
    private static boolean forcedSessionLanded(Corpus corpus,
                                               OccurrenceAddress anchor) {
        return !corpus.forcedPaths(anchor).isEmpty();
    }
}
