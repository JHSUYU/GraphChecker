package edu.uva.liftlab.graphchecker.runtime.d3;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;

/**
 * Where a point is in a component's control structure: the path of call
 * sites to it, each with the iteration of the innermost loop enclosing it.
 *
 * <p>IDENTITY-V3 §1, after Execution Indexing (PLDI 2008) and PEPID (ASE
 * 2013).  A flat ordinal -- "the 17th activation", "the k-th attach" --
 * moves whenever an unrelated invocation is inserted somewhere else in the
 * run, which is exactly what a branch flip does.  A call-site path does not:
 * an extra call elsewhere leaves it alone, and an extra iteration of a loop
 * ON the path moves it, which is inherent rather than accidental.</p>
 */
public final class ExecutionIndex {
    public static final ExecutionIndex EMPTY =
            new ExecutionIndex(Collections.<Frame>emptyList());

    private final List<Frame> frames;

    private ExecutionIndex(List<Frame> frames) {
        this.frames = Collections.unmodifiableList(frames);
    }

    public static ExecutionIndex of(List<Frame> frames) {
        return frames == null || frames.isEmpty() ? EMPTY
                : new ExecutionIndex(new ArrayList<Frame>(frames));
    }

    /** One frame of the path: a static call site and its loop iteration. */
    public static final class Frame {
        private final String callSiteId;
        private final int iteration;

        private Frame(String callSiteId, int iteration) {
            this.callSiteId = callSiteId;
            this.iteration = iteration;
        }

        public static Frame of(String callSiteId, int iteration) {
            return new Frame(Text.safe(callSiteId), Math.max(0, iteration));
        }

        public String callSiteId() {
            return callSiteId;
        }

        /** The innermost enclosing loop's iteration, 0 when not in one. */
        public int iteration() {
            return iteration;
        }

        public String render() {
            return callSiteId + "@" + iteration;
        }

        @Override
        public boolean equals(Object value) {
            if (this == value) return true;
            if (!(value instanceof Frame)) return false;
            Frame other = (Frame) value;
            return iteration == other.iteration
                    && callSiteId.equals(other.callSiteId);
        }

        @Override
        public int hashCode() {
            return Objects.hash(callSiteId, iteration);
        }

        @Override
        public String toString() {
            return render();
        }
    }

    public List<Frame> frames() {
        return frames;
    }

    public boolean isEmpty() {
        return frames.isEmpty();
    }

    /** The part of this index below {@code prefix}, or the whole of it. */
    public ExecutionIndex since(ExecutionIndex prefix) {
        if (prefix == null || prefix.isEmpty()) return this;
        int shared = 0;
        while (shared < frames.size() && shared < prefix.frames.size()
                && frames.get(shared).equals(prefix.frames.get(shared))) {
            shared++;
        }
        return shared == 0 ? this
                : of(new ArrayList<Frame>(
                        frames.subList(shared, frames.size())));
    }

    public String render() {
        StringBuilder rendered = new StringBuilder();
        for (Frame frame : frames) {
            if (rendered.length() > 0) rendered.append('/');
            rendered.append(frame.render());
        }
        return rendered.toString();
    }

    @Override
    public boolean equals(Object value) {
        return value instanceof ExecutionIndex
                && frames.equals(((ExecutionIndex) value).frames);
    }

    @Override
    public int hashCode() {
        return frames.hashCode();
    }

    @Override
    public String toString() {
        return render();
    }
}
