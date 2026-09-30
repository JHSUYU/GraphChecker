package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * One activation's frame stack, sampled on the VM's own event clock, so a
 * logged event read out after the activation still gets the frames it ran
 * on (IDENTITY §4).
 *
 * <ol>
 *   <li>Version ids and read event ids share one monotone session counter
 *       ({@code GlobalSymbolicSession::next_event_id}).</li>
 *   <li>Only the running thread appends, at every frame transition, with
 *       the clock after the transition.</li>
 *   <li>So event {@code E} stood on the frames of the LAST entry whose
 *       clock is below {@code E}.</li>
 *   <li>Journals are keyed by the {@code regionEnterEventId} every logged
 *       event states, so no event is resolved against another thread.</li>
 * </ol>
 *
 * <p>An entry whose interval is empty is replaced by the next.  An event the
 * journal cannot place gets null from {@link #framesAt}; the caller names
 * the gap.</p>
 */
public final class FrameJournal {
    /** Where the event clock comes from; see {@link Identity#clock}. */
    public interface Clock {
        /** The last published event id, or negative when there is none. */
        long now();
    }

    private static final Map<Long, FrameJournal> JOURNALS =
            new ConcurrentHashMap<Long, FrameJournal>();

    /** Clock readings, ascending, and the frames live at each. */
    private final List<Long> clocks = new ArrayList<Long>();
    private final List<Frame[]> frames = new ArrayList<Frame[]>();
    /**
     * Each entry's index, built at the first event read out on it: an entry
     * places every event of its interval, and the running thread only
     * copies its frames.
     */
    private final List<ExecutionIndex> indices =
            new ArrayList<ExecutionIndex>();

    private FrameJournal() {
    }

    /**
     * Opens one activation's journal, replacing any earlier one (a session
     * re-opened in one JVM restarts the counter).
     */
    static FrameJournal open(long activationKey, Frame[] atEntry) {
        FrameJournal journal = new FrameJournal();
        journal.note(activationKey, atEntry);
        JOURNALS.put(Long.valueOf(activationKey), journal);
        return journal;
    }

    synchronized void note(long now, Frame[] standing) {
        if (now < 0L) return;
        Frame[] copy = standing == null ? new Frame[0]
                : Arrays.copyOf(standing, standing.length);
        int last = clocks.size() - 1;
        if (last >= 0 && clocks.get(last) == now) {
            // Empty interval: the previous entry can place no event.
            frames.set(last, copy);
            indices.set(last, null);
            return;
        }
        if (last >= 0 && clocks.get(last) > now) {
            // A backwards reading is not this session's.
            return;
        }
        clocks.add(now);
        frames.add(copy);
        indices.add(null);
    }

    /** The frames live when {@code eventId} happened, or null. */
    private synchronized ExecutionIndex at(long eventId) {
        int low = 0;
        int high = clocks.size() - 1;
        int found = -1;
        while (low <= high) {
            int middle = (low + high) >>> 1;
            if (clocks.get(middle) < eventId) {
                found = middle;
                low = middle + 1;
            } else {
                high = middle - 1;
            }
        }
        if (found < 0) return null;
        ExecutionIndex index = indices.get(found);
        if (index == null) {
            index = ExecutionIndex.of(Arrays.asList(frames.get(found)));
            indices.set(found, index);
        }
        return index;
    }

    /**
     * The site index of one logged event, or null.
     *
     * @param activationKey the {@code regionEnterEventId} the event states
     * @param eventId       its version id or read event id
     */
    public static ExecutionIndex framesAt(long activationKey, long eventId) {
        if (activationKey <= 0L || eventId < 0L) return null;
        FrameJournal journal = JOURNALS.get(Long.valueOf(activationKey));
        return journal == null ? null : journal.at(eventId);
    }

    static void resetForTests() {
        JOURNALS.clear();
    }
}
