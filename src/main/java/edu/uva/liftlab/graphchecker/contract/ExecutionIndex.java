package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;

/**
 * IDENTITY-IMPL A: where in a component's control structure a point is --
 * frames from scope root to region entry (occurrence) or region entry to
 * event (site index), plus their 16-hex fold
 * {@code fold(h, f) = sha16(h + "/" + f.callSite + "@" + f.iteration)}.  The
 * runtime folds incrementally with the same function.
 */
public final class ExecutionIndex {
    /** The fold's seed: the hash of the index with no frames at all. */
    private static final String SEED = ArtifactIO.digest("", 16);

    private static final ExecutionIndex EMPTY =
            new ExecutionIndex(Collections.<Frame>emptyList(), SEED);

    private final List<Frame> frames;
    private final String hash;

    private ExecutionIndex(List<Frame> frames, String hash) {
        this.frames = frames;
        this.hash = hash;
    }

    public static ExecutionIndex empty() {
        return EMPTY;
    }

    public static ExecutionIndex of(List<Frame> frames) {
        List<Frame> copied = Fields.copy(frames);
        if (copied.isEmpty()) return EMPTY;
        String folded = SEED;
        for (Frame frame : copied) {
            folded = fold(folded, frame);
        }
        return new ExecutionIndex(copied, folded);
    }

    /** Reads {@code callSite@iter/callSite@iter/...}; {@code ""} is empty. */
    public static ExecutionIndex parse(String rendered) {
        String value = rendered == null ? "" : rendered.trim();
        if (value.isEmpty()) return EMPTY;
        List<Frame> frames = new ArrayList<>();
        int index = 0;
        while (index <= value.length()) {
            int next = value.indexOf('/', index);
            int end = next < 0 ? value.length() : next;
            frames.add(Frame.parse(value.substring(index, end)));
            if (next < 0) break;
            index = next + 1;
        }
        return of(frames);
    }

    /** The frames, outermost first. */
    public List<Frame> frames() {
        return frames;
    }

    /** The 16-hex fold of the frames: what an id is composed from. */
    public String hash() {
        return hash;
    }

    public int depth() {
        return frames.size();
    }

    public boolean isEmpty() {
        return frames.isEmpty();
    }

    public String render() {
        StringBuilder rendered = new StringBuilder();
        for (Frame frame : frames) {
            if (rendered.length() > 0) rendered.append('/');
            rendered.append(frame.render());
        }
        return rendered.toString();
    }

    private static String fold(String hash, Frame frame) {
        return ArtifactIO.digest(hash + "/" + frame.callSite() + "@"
                + frame.iteration(), 16);
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof ExecutionIndex)) return false;
        return frames.equals(((ExecutionIndex) value).frames);
    }

    @Override
    public int hashCode() {
        return Objects.hash(frames);
    }

    @Override
    public String toString() {
        return frames.isEmpty() ? "<no frames>" : render();
    }
}
