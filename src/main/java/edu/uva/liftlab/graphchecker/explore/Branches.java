package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.SessionReader;

import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * WHICH SESSIONS MAY PARENT AN OBLIGATION (PIPELINE §7.4).
 *
 * <p>The question is one declared occurrence {@code (r,c,i)}.  A focused
 * replay whose run holds no activation of the declared region {@code r}
 * under the declared context {@code c} -- at any invocation index {@code i},
 * since a flip may shift it (a fault's retry, a loop that runs once more) --
 * ran the question's occurrence under another chain or not at all
 * ({@code TASK_UNANSWERED}, {@code OCCURRENCE_ANCHOR_UNMATCHED}), so it can
 * answer nothing about it: its BRANCH STOPS.  Its world is never inherited,
 * its paths are never flipped and nothing it exposes is grown; it stays in
 * the corpus as the evidence it is (its rows still attest arms), and each
 * stop is a DIAGNOSTIC gap of the round that applied it.  Contexts compare by
 * {@link ContextShape} ({@link Corpus#contextShape}), the rule PLAN picks its
 * walk origins by.  COMPOSE and the claim stay on the exact declared
 * address.</p>
 */
public final class Branches {
    private final Corpus corpus;
    private final Set<String> stopped;

    private Branches(Corpus corpus, Set<String> stopped) {
        this.corpus = corpus;
        this.stopped = stopped;
    }

    /** Applies the rule to every admitted focused session of the corpus,
     *  naming each stop in {@code gaps}.  No resolved root stops none. */
    public static Branches of(Corpus corpus, List<OccurrenceAddress> roots,
                       List<GapRow> gaps) {
        Map<CausalContext, List<String>> shapes =
                new HashMap<CausalContext, List<String>>();
        Set<String> stopped = new LinkedHashSet<String>();
        for (SessionReader session : corpus.sessions()) {
            if (roots.isEmpty() || session.seed() || !session.admitted()) {
                continue;
            }
            if (holds(corpus, session, roots, shapes)) continue;
            stopped.add(session.sessionId());
            OccurrenceAddress root = roots.get(0);
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    session.sessionId(), "BRANCH_STOPPED: this replay ran "
                            + "no activation of the declared region "
                            + root.regionId() + " on "
                            + root.node().render() + " under the declared "
                            + "context " + root.context().render()
                            + ", at any index, so it can answer nothing "
                            + "about the declared occurrence: no "
                            + "obligation is cut from it or grown from it"));
        }
        return new Branches(corpus, stopped);
    }

    /** Whether a session may parent obligations: the seed, or an admitted
     *  focused session whose branch did not stop. */
    public boolean parents(String sessionId) {
        SessionReader session = corpus.session(sessionId);
        return session != null && session.admitted()
                && !stopped.contains(sessionId);
    }

    /** How many admitted focused sessions this round stopped. */
    public int stopped() {
        return stopped.size();
    }

    private static boolean holds(Corpus corpus, SessionReader session,
                                 List<OccurrenceAddress> roots,
                                 Map<CausalContext, List<String>> shapes) {
        for (ActivationRow activation : session.activations()) {
            for (OccurrenceAddress root : roots) {
                if (ContextShape.sameQuestion(activation.occurrence(), root,
                        context -> shapes.computeIfAbsent(context,
                                corpus::contextShape))) {
                    return true;
                }
            }
        }
        return false;
    }
}
