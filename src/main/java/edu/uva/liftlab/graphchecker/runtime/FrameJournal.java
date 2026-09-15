package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * One activation's frame stack, sampled on the VM's own event clock.
 *
 * <p>IDENTITY-IMPL §B computes an endpoint's site index AT the event.  The
 * events the VM logs -- a published version, a planned read -- are not at a
 * woven site, and the runtime reads them out at the end of the activation, by
 * which point the frames of the event are gone.  This is the alignment that
 * gives those events their frames without asking the VM for anything it does
 * not already say:</p>
 *
 * <ol>
 *   <li>Every version id and every read event id comes from one session-wide
 *       monotone counter ({@code GlobalSymbolicSession::next_event_id}), and
 *       {@code System.currentSymbolicEventId()} reads that counter.</li>
 *   <li>The journal of an activation is appended to only by the thread
 *       running it, at every frame transition of its execution index, with
 *       the clock as it stands after the transition.  Between two
 *       consecutive entries the thread's frames did not change.</li>
 *   <li>An event this thread published while standing between entry
 *       {@code i} and entry {@code i+1} therefore has an id in
 *       {@code (e_i, e_(i+1)]}: it was minted after the clock was read at
 *       {@code i} (the counter only grows) and before it was read at
 *       {@code i+1}.  So the frames of event {@code E} are those of the LAST
 *       entry whose clock is below {@code E}.</li>
 *   <li>Which journal: every logged event states the
 *       {@code regionEnterEventId} of the region activation that was
 *       innermost on its thread when it happened, and an activation's
 *       journal is filed under exactly that id.  So an event is never
 *       resolved against another thread's frames, which is what makes the
 *       interval argument above sound.</li>
 * </ol>
 *
 * <p>Entries whose interval holds no event are collapsed: a transition that
 * finds the clock where the previous entry left it replaces that entry, since
 * an empty interval can hold no event.  The journal is therefore as long as
 * the events of the activation, not as long as its calls.</p>
 *
 * <p>Nothing here is an ordinal: an entry is identified by a clock reading the
 * VM minted, and the answer is a set of frames the thread really stood on.  An
 * event the journal cannot place is unplaced -- {@link #framesAt} answers
 * null, and the caller names the gap.</p>
 */
public final class FrameJournal {
    /** Where the event clock comes from; see {@link Identity#clock}. */
    public interface Clock {
        /**
         * The id of the last event the VM's symbolic session published, or a
         * negative value when this run has no such clock.
         */
        long now();
    }

    /** Journals by the VM region-enter event id of their activation. */
    private static final Map<Long, FrameJournal> JOURNALS =
            new ConcurrentHashMap<Long, FrameJournal>();

    /** Clock readings, ascending, and the frames live at each. */
    private final List<long[]> clocks = new ArrayList<long[]>();
    private final List<Frame[]> frames = new ArrayList<Frame[]>();

    private FrameJournal() {
    }

    /**
     * Opens the journal of one activation, replacing any earlier one.
     *
     * <p>Region-enter event ids come from the same never-reused counter, so
     * one id is one activation; replacing is what happens when a session is
     * re-opened inside one JVM and the counter restarts.</p>
     */
    static FrameJournal open(long activationKey, Frame[] atEntry) {
        FrameJournal journal = new FrameJournal();
        journal.note(activationKey, atEntry);
        JOURNALS.put(Long.valueOf(activationKey), journal);
        return journal;
    }

    /** Records the frames this activation stands on at clock {@code now}. */
    synchronized void note(long now, Frame[] standing) {
        if (now < 0L) return;
        Frame[] copy = standing == null ? new Frame[0]
                : Arrays.copyOf(standing, standing.length);
        int last = clocks.size() - 1;
        if (last >= 0 && clocks.get(last)[0] == now) {
            // No event was published while the previous entry stood, so its
            // interval can hold none and it states nothing a reader needs.
            frames.set(last, copy);
            return;
        }
        if (last >= 0 && clocks.get(last)[0] > now) {
            // The clock only grows; a reading below the last one is not this
            // session's and would break the interval argument.
            return;
        }
        clocks.add(new long[]{now});
        frames.add(copy);
    }

    /** The frames live when {@code eventId} happened, or null. */
    private synchronized Frame[] at(long eventId) {
        int low = 0;
        int high = clocks.size() - 1;
        int found = -1;
        while (low <= high) {
            int middle = (low + high) >>> 1;
            if (clocks.get(middle)[0] < eventId) {
                found = middle;
                low = middle + 1;
            } else {
                high = middle - 1;
            }
        }
        return found < 0 ? null : frames.get(found);
    }

    /**
     * The site index of one logged event, or null when the run cannot say.
     *
     * @param activationKey the {@code regionEnterEventId} the event states
     * @param eventId       the version id or read event id of the event
     */
    public static ExecutionIndex framesAt(long activationKey, long eventId) {
        if (activationKey <= 0L || eventId < 0L) return null;
        FrameJournal journal = JOURNALS.get(Long.valueOf(activationKey));
        if (journal == null) return null;
        Frame[] standing = journal.at(eventId);
        if (standing == null) return null;
        return ExecutionIndex.of(Arrays.asList(standing));
    }

    static void resetForTests() {
        JOURNALS.clear();
    }
}
