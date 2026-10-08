package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.plan.ForcingTable;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * EXPLORE's half of the forced replay (PIPELINE §7.10).  Every campaign's
 * first round asks ONE FORCE run of the declared anchor's task, queued
 * first: the recording's world with the anchor's branches forced to the
 * throw ({@code runtime.ForcedArms}).  Its forced session lands held apart
 * ({@code Corpus#forcedPaths}) and parents one forced flip ({@link
 * ObligationFactory#forced}), the anchor's whole fatal condition asked at
 * once.  The seed path's flips at the forcing table's sites wait -- deferred,
 * never dropped -- while the FORCE run or the forced flip is unanswered: the
 * forced condition first, the nested flips only where it brought no witness.
 */
final class ForcedFlip {
    /** How a FORCE worker's verdict detail opens. */
    static final String FORCE = "FORCE";

    /** One round's forced share. */
    static final class Round {
        /** The FORCE obligation while it is owed, else null. */
        final Obligation force;
        /** The candidates: the forced flips first, deferred ones out. */
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
     * obligation while no round answered it and none flies; the forced
     * flips, first; and the seed path's flips at a site of the forcing table
     * held back while the FORCE run or a forced flip is unanswered (each a
     * DIAGNOSTIC gap).
     */
    static Round plan(Corpus corpus, Task anchor, StaticScopeMap scope,
                      Frontier frontier, List<ObligationResult> results,
                      List<ObligationFactory.Candidate> candidates,
                      List<GapRow> gaps) {
        JsonObject manifest = new JsonObject();
        Set<String> sites = ForcingTable.read(scope.forcing()).keySet();
        if (anchor == null || sites.isEmpty()) {
            // No table, nothing to force: the seed's way stands alone.
            manifest.addProperty("state", "NO_FORCING_TABLE");
            return new Round(null, candidates, manifest);
        }
        Obligation force = force(corpus, anchor);
        Verdict answered = frontier.verdict(force.obligationId());
        boolean forceOpen = answered == null
                || answered == Verdict.SAT_MODEL_READY;
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
        boolean flipOpen = false;
        int settled = 0;
        for (ObligationFactory.Candidate flip : forced) {
            String reason = frontier.settled(flip.obligationId);
            if (reason.isEmpty()) {
                flipOpen = true;
            } else {
                settled++;
            }
            manifest.addProperty("forcedFlip", flip.obligationId);
            manifest.addProperty("forcedFlipVerdict", reason.isEmpty()
                    ? "OPEN" : String.valueOf(frontier.verdict(
                    flip.obligationId)));
        }
        manifest.addProperty("forcedPaths", forced.size());
        boolean holding = forceOpen || flipOpen;
        String seed = corpus.seedSessionId();
        List<ObligationFactory.Candidate> round =
                new ArrayList<ObligationFactory.Candidate>(forced);
        int deferred = 0;
        int after = 0;
        for (ObligationFactory.Candidate candidate : candidates) {
            boolean atForced = candidate.task.taskId().equals(
                    anchor.taskId()) && seed.equals(candidate.path.sessionId)
                    && sites.contains(candidate.decision.siteId());
            if (atForced && holding) {
                deferred++;
                gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                        GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        candidate.decision.siteId() + "#"
                                + candidate.decision.ordinal(),
                        "deferred behind the forced replay: the seed path's"
                                + " flip at a site of the forcing table waits"
                                + " until the FORCE run and its forced flip"
                                + " are answered"));
                continue;
            }
            // Asked after the forced flip was answered: what the follow-up
            // deletion is decided on (PIPELINE §7.10).
            if (atForced && settled > 0
                    && frontier.settled(candidate.obligationId).isEmpty()
                    && !frontier.flying(candidate)) {
                after++;
            }
            round.add(candidate);
        }
        manifest.addProperty("deferredSeedFlips", deferred);
        manifest.addProperty("seedFlipsAfterForcedFlip", after);
        return new Round(forceOpen && !forcedSessionLanded(corpus,
                anchor.focused()) ? force : null, round, manifest);
    }

    /** Whether a forced session of this occurrence is in the corpus: its
     *  FORCE run was answered, whatever the ledger reads. */
    private static boolean forcedSessionLanded(Corpus corpus,
                                               OccurrenceAddress anchor) {
        return !corpus.forcedPaths(anchor).isEmpty();
    }
}
