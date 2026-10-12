package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.runtime.Confirmation;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * THE PAIRING FLIP (PIPELINE §7.4, SYMBOL-SCOPE §6.4): a read of a node's
 * VIEW of a store location takes an older decode of that node.  A node
 * decides on whichever decode its view held, and a view is late by the
 * delivery of a watch; what a stale view changes is often no value a term
 * names -- a key absent from an older document, a replica a loop skips --,
 * so no decision's flip reaches it.  The flip asks the path as its
 * session ran it, up to the read, with the read paired to the node's
 * decode of the older version, and plants that pairing: CONFIRM's rows
 * hold it (ConfirmMain#holding, a VIEW_HOLD per pairing, PIPELINE §7.5), and the replay
 * is admitted when the read observed that version.
 *
 * <p>Candidates (one task path): the VIEW reads of its occurrence, and
 * those its node made under its causal context before it opened -- a
 * routed alias captures its node's view in the request's role work and
 * writes it in a store door's region -- where the occurrence writes a STORE
 * version or is the declared anchor's (a stale view sits at the reader
 * too).  Per read of a view (its earliest in that work), each older version
 * the node decoded before it in the session, newest first, at most {@link
 * #PER_READ}; past them a {@code pairing-bound} gap, counted in result.json
 * {@code bounded}.</p>
 */
final class PairingFlip {
    /** The most older decodes one read of a view is offered. */
    static final int PER_READ = 8;
    /** The bound's name, in its gap's subject ({@code campaign_bounds}). */
    static final String BOUND = "pairing-bound";
    /** The dependence every pairing flip's id carries: the question is the
     *  read and the version, whatever the guards. */
    private static final String DEPENDENCE = "VIEW";

    private PairingFlip() {
    }

    /** A pairing flip's site: {@link Obligation#PAIRING} and its read. */
    static String site(ReadRow read) {
        return Obligation.PAIRING + Confirmation.id(read.endpoint());
    }

    /** A pairing flip's ordinal: the version it asks plus one, an ordinal
     *  being 1-based ({@link Obligation#pairedVersion}). */
    static int ordinal(long version) {
        return Math.toIntExact(version + 1L);
    }

    /**
     * The pairing flips one path of {@code task} offers, newest version
     * first per read; a read offered more than {@link #PER_READ} files the
     * bound's gap.  None older than a decode the reader's own work made
     * before the read: the hold never holds the reader's own decodes
     * ({@code Confirmation#decoding}), so the view is at least that one's.
     */
    static List<ObligationFactory.Candidate> candidates(Corpus corpus,
            Task task, Corpus.RecordedPath path, List<GapRow> gaps) {
        List<ObligationFactory.Candidate> offered =
                new ArrayList<ObligationFactory.Candidate>();
        SessionReader session = corpus.session(path.sessionId);
        if (session == null || !offers(corpus, task, session)) {
            return offered;
        }
        for (ReadRow read : reads(corpus, task, session)) {
            String view = SmtLowering.locationKey(read.location());
            String reader = Confirmation.contextKey(
                    read.endpoint().occurrence());
            long floor = -1L;
            for (WriteRow decode : corpus.writesOf(path.sessionId, view)) {
                if (decode.seq() < read.seq() && reader.equals(Confirmation
                        .contextKey(decode.endpoint().occurrence()))) {
                    floor = Math.max(floor, decode.version());
                }
            }
            Set<Long> older = new TreeSet<Long>(Collections.reverseOrder());
            for (WriteRow decode : corpus.writesOf(path.sessionId, view)) {
                if (decode.seq() < read.seq() && decode.version() >= floor
                        && decode.version() < read.observedVersion()) {
                    older.add(decode.version());
                }
            }
            int asked = 0;
            for (long version : older) {
                if (asked++ == PER_READ) {
                    gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                            GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                            task.taskId() + " " + BOUND + "=" + PER_READ,
                            "read " + read.endpoint() + " of " + view
                                    + " observed version "
                                    + read.observedVersion() + " and its node"
                                    + " decoded " + older.size() + " older"
                                    + " ones before it: the " + PER_READ
                                    + " newest are offered, the rest never"));
                    break;
                }
                offered.add(new ObligationFactory.Candidate(task, path, read,
                        version, ObligationFactory.obligationId(
                        task.taskId(), site(read), ordinal(version), true,
                        DEPENDENCE)));
            }
        }
        return offered;
    }

    /**
     * Whether a task offers pairing flips: its occurrence writes a STORE
     * version in this session, or it is the declared anchor's.
     */
    private static boolean offers(Corpus corpus, Task task,
                                  SessionReader session) {
        if (!corpus.targetsOn(task.focused()).isEmpty()) return true;
        for (WriteRow write : session.writes()) {
            if (write.location().kind() == LocationKind.STORE
                    && write.endpoint().occurrence().equals(task.focused())) {
                return true;
            }
        }
        return false;
    }

    /**
     * The view reads a task's path offers: its occurrence's, and its
     * node's under its causal context in role work before it opened (its
     * first row), the earliest per view.
     */
    private static List<ReadRow> reads(Corpus corpus, Task task,
                                       SessionReader session) {
        OccurrenceAddress focused = task.focused();
        long opened = Long.MAX_VALUE;
        for (ReadRow read : corpus.readsOn(session.sessionId(), focused)) {
            opened = Math.min(opened, read.seq());
        }
        for (WriteRow write : session.writes()) {
            if (write.endpoint().occurrence().equals(focused)) {
                opened = Math.min(opened, write.seq());
            }
        }
        Map<String, ReadRow> earliest = new LinkedHashMap<String, ReadRow>();
        for (ReadRow read : session.reads()) {
            if (read.location().kind() != LocationKind.VIEW
                    || read.observedVersion() < 0L) {
                continue;
            }
            OccurrenceAddress at = read.endpoint().occurrence();
            boolean own = at.equals(focused);
            boolean prefix = !own && at.role()
                    && at.node().equals(focused.node())
                    && at.context().equals(focused.context())
                    && read.seq() < opened;
            if (!own && !prefix) continue;
            String view = SmtLowering.locationKey(read.location());
            ReadRow held = earliest.get(view);
            if (held == null || read.seq() < held.seq()) {
                earliest.put(view, read);
            }
        }
        return new ArrayList<ReadRow>(earliest.values());
    }

    /** The pairing flip a published obligation names on its path, or
     *  null where the path states no such read. */
    static ObligationFactory.Candidate locate(Corpus corpus, Task task,
                                              Corpus.RecordedPath path,
                                              Obligation obligation) {
        SessionReader session = corpus.session(path.sessionId);
        if (session == null) return null;
        for (ReadRow read : session.reads()) {
            if (read.location().kind() == LocationKind.VIEW
                    && site(read).equals(obligation.siteId())) {
                return new ObligationFactory.Candidate(task, path, read,
                        obligation.pairedVersion(), obligation.obligationId());
            }
        }
        return null;
    }

    /**
     * One pairing flip, solved: no query is asked -- the path is the one its
     * session ran, up to the read -- and the world is the session's with the
     * read paired to the decode of the asked version, held by CONFIRM's rows
     * over that session ({@link ConfirmMain#holding}); or the answer of the
     * same question a worker settled.
     */
    static ObligationFactory.Outcome solve(Corpus corpus,
            ObligationFactory.Candidate candidate, String given,
            Map<String, ObligationDir.Answer> answered) {
        String id = candidate.obligationId;
        ReadRow read = candidate.pairedRead;
        Corpus.World inherited = corpus.world(candidate.path.sessionId);
        Map<String, String> paired = new LinkedHashMap<String, String>();
        paired.put(Confirmation.id(read.endpoint()),
                Confirmation.viewWriter(candidate.pairedVersion));
        Map<String, String> pairings =
                ObligationFactory.overlay(inherited.pairings, paired);
        String question = question(candidate, inherited, paired, given);
        List<GapRow> gaps = new ArrayList<GapRow>();
        ObligationDir.Answer earlier = answered.get(question);
        if (earlier != null && earlier.result.refutation() == null
                && !earlier.result.worldUnrefuted()) {
            String detail = "question " + question + " was settled "
                    + earlier.result.verdict() + " by obligation "
                    + earlier.obligationId + ", which asked the same read"
                    + " of the same view and world: "
                    + earlier.result.detail();
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC, id, detail));
            return ObligationFactory.refused(candidate,
                    earlier.result.verdict(), detail, "", gaps, question,
                    false);
        }
        ConfirmMain.Holding holding;
        try {
            holding = ConfirmMain.holding(
                    corpus.session(candidate.path.sessionId), pairings);
        } catch (ConfirmMain.Refused unheld) {
            return ObligationFactory.refused(candidate, Verdict.NOT_ADMITTED,
                    unheld.getMessage(), "", gaps, question, true);
        }
        // The inherited roots are planted at their mints, as a flip's are.
        Map<String, String> mints = new LinkedHashMap<String, String>();
        Set<String> assigned = new LinkedHashSet<String>(
                inherited.rootAssignments.keySet());
        assigned.addAll(inherited.clockDeltas.keySet());
        for (String rootId : assigned) {
            RootMintRow mint = corpus.rootOf(corpus.seedSessionId(), rootId);
            if (mint != null) mints.put(rootId, mint.occurrence().render());
        }
        Obligation solved = Obligation.of(id, candidate.task.taskId(),
                candidate.path.pathId, candidate.siteId(),
                candidate.ordinal(), true, inherited.rootAssignments,
                inherited.answers, Collections.<String>emptyList());
        return new ObligationFactory.Outcome(solved, ObligationResult.of(id,
                Verdict.SAT_MODEL_READY, "", "read " + read.endpoint()
                        + " of " + read.location() + " takes its node's"
                        + " decode of version " + candidate.pairedVersion
                        + " (it observed " + read.observedVersion() + "), in"
                        + " the world of " + candidate.path.sessionId
                        + " with " + pairings.size() + " planted"
                        + " pairing(s)"), "",
                new LinkedHashMap<String, String>(inherited.clockDeltas),
                mints, inherited.flips, pairings, holding, gaps, question,
                true, false);
    }

    /** The question a pairing flip asks: the flip, then a digest of the
     *  world it extends, the pairing, the focus, the factor, the seed and
     *  what the replay is given ({@code ObligationFactory#question}). */
    private static String question(ObligationFactory.Candidate candidate,
                                   Corpus.World world,
                                   Map<String, String> paired, String given) {
        StringBuilder text = new StringBuilder("pairing ")
                .append(paired).append('\n')
                .append(ObligationFactory.worldText(world))
                .append("\nfocused ").append(candidate.task.focused().id())
                .append("\nseed ").append(candidate.task.seedSessionId());
        Set<String> factor = new TreeSet<String>();
        for (OccurrenceAddress member : candidate.task.factor()) {
            factor.add(member.id());
        }
        for (String member : factor) text.append("\nfactor ").append(member);
        text.append('\n').append(given);
        return ObligationFactory.flip(candidate) + ":"
                + ArtifactIO.digest(text.toString(), 16);
    }
}
