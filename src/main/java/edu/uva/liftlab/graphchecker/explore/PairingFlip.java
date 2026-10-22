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
import edu.uva.liftlab.graphchecker.contract.RowOrder;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.runtime.Confirmation;
import edu.uva.liftlab.graphchecker.runtime.MessageDoors;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

final class PairingFlip {
    static final int PER_READ = 8;
    static final String BOUND = "pairing-bound";
    private static final String DEPENDENCE = "VIEW";
    private static final String STORE_DEPENDENCE = "STORE";

    private PairingFlip() {
    }

    static String site(ReadRow read) {
        return Obligation.PAIRING + Confirmation.id(read.endpoint());
    }

    static int ordinal(long version) {
        return Math.toIntExact(version + 1L);
    }

    static List<ObligationFactory.Candidate> candidates(Corpus corpus,
            Task task, Corpus.RecordedPath path, List<GapRow> gaps) {
        List<ObligationFactory.Candidate> offered =
                new ArrayList<ObligationFactory.Candidate>();
        SessionReader session = corpus.session(path.sessionId);
        if (session == null || !offers(corpus, task, session)) {
            return offered;
        }
        for (ReadRow read : reads(corpus, task, session)) {
            if (read.location().kind() == LocationKind.STORE) {
                offered.addAll(tombstones(corpus, task, path, read));
                continue;
            }
            if (!Confirmation.hookPublishes(read.location())) {
                gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                        GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC, site(read),
                        "no publication hook publishes " + read.location()
                                + " (its system states no PUBLISHED_VIEW of"
                                + " it), so no hold can defer it: no pairing"
                                + " of the read is asked"));
                continue;
            }
            String view = SmtLowering.locationKey(read.location());
            String reader = Confirmation.contextKey(
                    read.endpoint().occurrence());
            long floor = -1L;
            for (WriteRow decode : corpus.writesOf(path.sessionId, view)) {
                if (decodedBefore(decode, read) && reader.equals(Confirmation
                        .contextKey(decode.endpoint().occurrence()))) {
                    floor = Math.max(floor, decode.version());
                }
            }
            Set<Long> older = new TreeSet<Long>(Collections.reverseOrder());
            for (WriteRow decode : corpus.writesOf(path.sessionId, view)) {
                if (decodedBefore(decode, read) && decode.version() >= floor
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

    private static List<ObligationFactory.Candidate> tombstones(
            Corpus corpus, Task task, Corpus.RecordedPath path,
            ReadRow read) {
        List<ObligationFactory.Candidate> offered =
                new ArrayList<ObligationFactory.Candidate>();
        String location = SmtLowering.locationKey(read.location());
        Set<Long> later = new TreeSet<Long>();
        for (WriteRow write : corpus.writesOf(path.sessionId, location)) {
            if (write.version() == MessageDoors.TOMBSTONE
                    && read.observedVersion() != MessageDoors.TOMBSTONE
                    && RowOrder.before(read, write)) {
                later.add(write.version());
            }
        }
        for (long version : later) {
            offered.add(new ObligationFactory.Candidate(task, path, read,
                    version, ObligationFactory.obligationId(task.taskId(),
                    site(read), ordinal(version), true, STORE_DEPENDENCE)));
        }
        return offered;
    }

    private static boolean decodedBefore(WriteRow decode, ReadRow read) {
        return decode.initial() || RowOrder.before(decode, read);
    }

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

    private static List<ReadRow> reads(Corpus corpus, Task task,
                                       SessionReader session) {
        OccurrenceAddress focused = task.focused();
        Map<String, ReadRow> earliest = new LinkedHashMap<String, ReadRow>();
        for (ReadRow read : session.reads()) {
            if (read.location().kind() != LocationKind.VIEW
                    && read.location().kind() != LocationKind.STORE
                    || read.observedVersion() < 0L) {
                continue;
            }
            if (!read.endpoint().occurrence().equals(focused)
                    && !corpus.rolePrefix(session.sessionId(), read,
                    focused)) {
                continue;
            }
            String view = SmtLowering.locationKey(read.location());
            ReadRow held = earliest.get(view);
            if (held == null || RowOrder.before(read.seq(), read.tie(),
                    held.seq(), held.tie())) {
                earliest.put(view, read);
            }
        }
        return new ArrayList<ReadRow>(earliest.values());
    }

    static ObligationFactory.Candidate locate(Corpus corpus, Task task,
                                              Corpus.RecordedPath path,
                                              Obligation obligation) {
        SessionReader session = corpus.session(path.sessionId);
        if (session == null) return null;
        for (ReadRow read : session.reads()) {
            if ((read.location().kind() == LocationKind.VIEW
                    || read.location().kind() == LocationKind.STORE)
                    && site(read).equals(obligation.siteId())) {
                return new ObligationFactory.Candidate(task, path, read,
                        obligation.pairedVersion(), obligation.obligationId());
            }
        }
        return null;
    }

    static ObligationFactory.Outcome solve(Corpus corpus,
            ObligationFactory.Candidate candidate, String given,
            Map<String, ObligationDir.Answer> answered) {
        String id = candidate.obligationId;
        ReadRow read = candidate.pairedRead;
        Corpus.World inherited = corpus.world(candidate.path.sessionId);
        Map<String, String> paired = new LinkedHashMap<String, String>();
        boolean store = read.location().kind() == LocationKind.STORE;
        paired.put(Confirmation.id(read.endpoint()), store
                ? Confirmation.storeWriter(candidate.pairedVersion)
                : Confirmation.viewWriter(candidate.pairedVersion));
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
        Map<String, String> mints = new LinkedHashMap<String, String>();
        Set<String> assigned = new LinkedHashSet<String>(
                inherited.rootAssignments.keySet());
        assigned.addAll(inherited.clockDeltas.keySet());
        for (String rootId : assigned) {
            RootMintRow mint = corpus.mintOf(candidate.path.sessionId,
                    rootId);
            if (mint != null) mints.put(rootId, mint.occurrence().render());
        }
        Obligation solved = Obligation.of(id, candidate.task.taskId(),
                candidate.path.pathId, candidate.siteId(),
                candidate.ordinal(), true, inherited.rootAssignments,
                inherited.answers, Collections.<String>emptyList());
        return new ObligationFactory.Outcome(solved, ObligationResult.of(id,
                Verdict.SAT_MODEL_READY, "", "read " + read.endpoint()
                        + " of " + read.location() + (store ? " takes the"
                        + " store's version " : " takes its node's decode of"
                        + " version ") + candidate.pairedVersion
                        + " (it observed " + read.observedVersion() + "), in"
                        + " the world of " + candidate.path.sessionId
                        + " with " + pairings.size() + " planted"
                        + " pairing(s)"), "",
                new LinkedHashMap<String, String>(inherited.clockDeltas),
                mints, inherited.flips, pairings, holding, gaps, question,
                true, false, null);
    }

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
