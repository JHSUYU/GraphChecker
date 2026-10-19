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

public final class Branches {
    private final Corpus corpus;
    private final Set<String> stopped;

    private Branches(Corpus corpus, Set<String> stopped) {
        this.corpus = corpus;
        this.stopped = stopped;
    }

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

    public boolean parents(String sessionId) {
        SessionReader session = corpus.session(sessionId);
        return session != null && session.admitted()
                && !stopped.contains(sessionId);
    }

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
