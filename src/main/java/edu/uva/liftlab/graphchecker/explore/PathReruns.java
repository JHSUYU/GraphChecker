package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Consumer;

final class PathReruns {
    static final String RERUN = "RERUN";

    private PathReruns() {
    }

    static List<Obligation> of(Corpus corpus, Task anchor,
                               Map<String, Set<OccurrenceAddress>> unrecorded,
                               Set<String> planned,
                               Consumer<GapRow> gaps) {
        List<Obligation> reruns = new ArrayList<Obligation>();
        if (anchor == null) return reruns;
        for (Map.Entry<String, Set<OccurrenceAddress>> reading
                : unrecorded.entrySet()) {
            String sessionId = reading.getKey();
            SessionReader session = corpus.session(sessionId);
            if (session == null || !session.manifest().seed()
                    && !session.manifest().forced()) {
                continue;
            }
            Set<String> writers = writers(corpus, sessionId,
                    reading.getValue(), planned);
            if (writers.isEmpty()) continue;
            Obligation rerun = session.manifest().forced()
                    ? forced(corpus, anchor, writers)
                    : recorded(corpus, anchor, sessionId, writers);
            if (rerun == null) continue;
            reruns.add(rerun);
            gaps.accept(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    RERUN + " " + rerun.obligationId(), "the anchor's path in "
                            + sessionId + " read values no row wrote, and "
                            + "their writers ran unplanned there and are "
                            + "planned now: its world is replayed with them "
                            + writers));
        }
        return reruns;
    }

    private static Set<String> writers(Corpus corpus, String sessionId,
                                       Collection<OccurrenceAddress> held,
                                       Set<String> planned) {
        Set<String> writers = new TreeSet<String>();
        for (OccurrenceAddress writer : held) {
            ActivationRow ran = corpus.activation(sessionId, writer);
            if (planned.contains(writer.render())
                    && (ran == null || !ran.instrumented())) {
                writers.add(writer.render());
            }
        }
        return writers;
    }

    private static Obligation forced(Corpus corpus, Task anchor,
                                     Set<String> writers) {
        return Obligation.forcing(id("force|" + anchor.taskId(), writers),
                anchor.taskId(), Corpus.pathId(corpus.seedSessionId(),
                        anchor.focused()));
    }

    private static Obligation recorded(Corpus corpus, Task anchor,
                                       String sessionId,
                                       Set<String> writers) {
        Corpus.RecordedPath path = corpus.path(sessionId, anchor.focused());
        if (path == null || path.decisions.isEmpty()) return null;
        TargetRow target = corpus.target(sessionId, anchor.focused());
        DecisionRow at = path.decisions.get(path.decisions.size() - 1);
        for (DecisionRow decision : path.decisions) {
            if (target != null && target.anchorSiteId().equals(
                    decision.siteId() + "#" + decision.ordinal())) {
                at = decision;
            }
        }
        return Obligation.rerunning(id(path.pathId, writers),
                anchor.taskId(), path.pathId, at.siteId(), at.ordinal(),
                at.outcome());
    }

    private static String id(String path, Set<String> writers) {
        return ArtifactIO.digest(RERUN + "|" + path + "|"
                + String.join("|", writers), 16);
    }
}
