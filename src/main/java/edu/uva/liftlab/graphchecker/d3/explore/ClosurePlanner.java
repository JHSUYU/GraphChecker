package edu.uva.liftlab.graphchecker.d3.explore;

import edu.uva.liftlab.graphchecker.d3.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.ExportRow;
import edu.uva.liftlab.graphchecker.d3.contract.GapClass;
import edu.uva.liftlab.graphchecker.d3.contract.GapKind;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.LocationId;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.Task;
import edu.uva.liftlab.graphchecker.d3.contract.WriteRow;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The anchor's closure, as a list of tasks.
 *
 * <p>The closure is what the anchor's failure can depend on, and nothing
 * else: the anchor occurrence itself, the PRODUCER of every interaction its
 * paths read (transitively -- a producer often forwards a value it was
 * itself handed, so its export names another {@code v_H} whose own producer
 * belongs to the closure too), the WRITER of every version its paths read,
 * and the occurrences its node's state connects it to (the writers and
 * readers of one location).</p>
 *
 * <p>Each closure element becomes one task with ONE focused occurrence, and
 * carries the co-occurrences it is state-connected to as its {@code factor}:
 * those replay symbolically with it, because a value in a container is
 * written by one activation and read by another on the same node, and
 * separating them would leave the read with nothing to join to.  The
 * producer of a wire interaction is never a factor -- it is another node's
 * activation and therefore its own task, explored on its own frontier and
 * admitted on its own prefix.</p>
 */
public final class ClosurePlanner {
    /** How many tasks one anchor may open, before the closure is truncated. */
    public static final int DEFAULT_MAX_TASKS = 64;

    private ClosurePlanner() {
    }

    /** The closure of one anchor, and what could not be named in it. */
    public static final class Plan {
        public final List<Task> tasks;
        public final List<GapRow> gaps;

        private Plan(List<Task> tasks, List<GapRow> gaps) {
            this.tasks = Collections.unmodifiableList(tasks);
            this.gaps = Collections.unmodifiableList(gaps);
        }
    }

    public static Plan plan(Corpus corpus, OccurrenceAddress anchor) {
        return plan(corpus, anchor, DEFAULT_MAX_TASKS);
    }

    public static Plan plan(Corpus corpus, OccurrenceAddress anchor,
                            int maxTasks) {
        List<Task> tasks = new ArrayList<Task>();
        List<GapRow> gaps = new ArrayList<GapRow>();
        Set<String> visited = new LinkedHashSet<String>();
        Deque<OccurrenceAddress> pending = new ArrayDeque<OccurrenceAddress>();
        pending.add(anchor);
        visited.add(anchor.id());
        while (!pending.isEmpty() && tasks.size() < maxTasks) {
            OccurrenceAddress occurrence = pending.remove();
            List<OccurrenceAddress> factor = stateConnected(corpus,
                    occurrence);
            tasks.add(Task.of(taskId(occurrence), occurrence, factor,
                    seedSession(corpus, occurrence)));
            for (OccurrenceAddress next
                    : successors(corpus, occurrence, factor, gaps)) {
                if (visited.add(next.id())) pending.add(next);
            }
        }
        if (!pending.isEmpty()) {
            gaps.add(GapRow.of("", GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    anchor.render(), "closure truncated at " + maxTasks
                            + " tasks; " + pending.size() + " occurrences "
                            + "were not planned"));
        }
        return new Plan(tasks, gaps);
    }

    /** One task's id: the occurrence it focuses and nothing else. */
    public static String taskId(OccurrenceAddress focused) {
        return ExploreIds.sha16("task|" + focused.id());
    }

    /**
     * The task one published obligation names.
     *
     * <p>A task id is its focused occurrence's id and nothing else, so the
     * worker that executes an obligation recovers the task from the corpus
     * rather than from a second file that could disagree with the wave's.</p>
     */
    public static Task taskOf(Corpus corpus, String taskId) {
        if (taskId == null || taskId.isEmpty()) return null;
        for (OccurrenceAddress occurrence : corpus.occurrences()) {
            if (!taskId.equals(taskId(occurrence))) continue;
            return Task.of(taskId, occurrence, stateConnected(corpus,
                    occurrence), seedSession(corpus, occurrence));
        }
        return null;
    }

    /**
     * Everything one occurrence's failure can depend on outside its own node
     * state: the producers of the interactions it reads and the writers of
     * the versions it reads, plus the co-occurrences its factor names, whose
     * own producers belong to the closure just as much.
     */
    private static List<OccurrenceAddress> successors(
            Corpus corpus, OccurrenceAddress occurrence,
            List<OccurrenceAddress> factor, List<GapRow> gaps) {
        List<OccurrenceAddress> next = new ArrayList<OccurrenceAddress>();
        List<OccurrenceAddress> group = new ArrayList<OccurrenceAddress>();
        group.add(occurrence);
        group.addAll(factor);
        for (OccurrenceAddress member : group) {
            if (!member.equals(occurrence)) next.add(member);
            for (AttachRow attach : corpus.attachesOn(member)) {
                producers(corpus, attach, next, gaps,
                        new LinkedHashSet<String>());
            }
            for (ReadRow read : corpus.readsOn(member)) {
                WriteRow writer = corpus.writeOf(read.sessionId(), read.location(),
                        read.observedVersion());
                if (writer != null) next.add(writer.endpoint().occurrence());
            }
        }
        return next;
    }

    /**
     * The producer of one attach, and the producers of every handoff its
     * delivery is forwarded from.
     *
     * <p>A key id an NN hands a balancer, which hands it to a data node, is
     * one value with two interactions; the first is in the closure of the
     * second's consumer.  Following the exported expression's own nested
     * handoff symbols is what makes the chain end at the mint rather than at
     * the first hop.</p>
     */
    private static void producers(Corpus corpus, AttachRow attach,
                                  List<OccurrenceAddress> into,
                                  List<GapRow> gaps, Set<String> seen) {
        if (attach == null || !seen.add(attach.endpoint().id())) return;
        if (attach.producer() == null) {
            gaps.add(GapRow.of(attach.sessionId(), GapKind.LINEAGE_LOST,
                    GapClass.DIAGNOSTIC, attach.endpoint().toString(),
                    "attach is unpaired: no producer endpoint to close over"));
            return;
        }
        into.add(attach.producer().occurrence());
        SessionReader.Session session = corpus.session(attach.sessionId());
        if (session == null) return;
        for (ExportRow export : corpus.exportsAt(attach.producer())) {
            SessionReader.Session exporting = corpus.session(export.sessionId());
            if (exporting == null) continue;
            SmtLowering.Lowered lowered =
                    exporting.lowering().lower(export.expressionRef());
            for (Map.Entry<String, String> symbol
                    : lowered.declarations().entrySet()) {
                AttachRow nested = corpus.attach(export.sessionId(),
                        symbol.getKey());
                if (nested != null) {
                    into.add(nested.endpoint().occurrence());
                    producers(corpus, nested, into, gaps, seen);
                }
            }
        }
    }

    /**
     * The co-occurrences one occurrence is state-connected to: the writers
     * and readers of a location it touches, on its own node.
     */
    private static List<OccurrenceAddress> stateConnected(
            Corpus corpus, OccurrenceAddress occurrence) {
        Set<LocationId> locations = new LinkedHashSet<LocationId>();
        for (ReadRow read : corpus.readsOn(occurrence)) {
            locations.add(read.location());
        }
        for (WriteRow write : corpus.writesOn(occurrence)) {
            locations.add(write.location());
        }
        Set<String> connected = new LinkedHashSet<String>();
        for (LocationId location : locations) {
            connected.addAll(corpus.touching(occurrence, location));
        }
        connected.remove(occurrence.id());
        List<OccurrenceAddress> factor = new ArrayList<OccurrenceAddress>();
        for (String id : connected) {
            OccurrenceAddress member = corpus.occurrence(id);
            if (member != null) factor.add(member);
        }
        return factor;
    }

    /** The session an occurrence was first recorded in. */
    private static String seedSession(Corpus corpus,
                                      OccurrenceAddress occurrence) {
        for (SessionReader.Session session : corpus.sessions()) {
            if (corpus.activation(session.sessionId, occurrence) != null
                    || !corpus.decisionsOf(session.sessionId, occurrence)
                    .isEmpty()) {
                return session.sessionId;
            }
        }
        return "";
    }
}
