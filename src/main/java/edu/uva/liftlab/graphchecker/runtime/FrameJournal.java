package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

public final class FrameJournal {
    public interface Clock {
        long now();
    }

    private static final Map<Long, FrameJournal> JOURNALS =
            new ConcurrentHashMap<Long, FrameJournal>();

    private final List<Long> clocks = new ArrayList<Long>();
    private final List<Frame[]> frames = new ArrayList<Frame[]>();
    private final List<ExecutionIndex> indices =
            new ArrayList<ExecutionIndex>();

    private FrameJournal() {
    }

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
            frames.set(last, copy);
            indices.set(last, null);
            return;
        }
        if (last >= 0 && clocks.get(last) > now) {
            return;
        }
        clocks.add(now);
        frames.add(copy);
        indices.add(null);
    }

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

    public static ExecutionIndex framesAt(long activationKey, long eventId) {
        if (activationKey <= 0L || eventId < 0L) return null;
        FrameJournal journal = JOURNALS.get(Long.valueOf(activationKey));
        return journal == null ? null : journal.at(eventId);
    }
}
