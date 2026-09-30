package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * CONTRACT-SPEC §1, IDENTITY §3: where in a component's control structure a
 * point is -- frames from scope root to region entry (occurrence) or region
 * entry to event (site index), plus their 16-hex fold
 * {@code fold(h, f) = sha16(h + "/" + f.callSite + "@" + f.iteration)}.
 *
 * <p>The fold and the rendering are derived, each at its first use: most
 * indices a replay builds are only rendered (a logged event's site index),
 * and a SHA-256 per frame per index was the publication thread's hot spot
 * in the concolic interpreter.  Folds repeat wherever indices share a
 * prefix, so each one is memoized.</p>
 */
public final class ExecutionIndex extends Value {
    /** The fold's seed: the hash of the index with no frames at all. */
    private static final String SEED = ArtifactIO.digest("", 16);

    private static final ExecutionIndex EMPTY =
            new ExecutionIndex(Collections.<Frame>emptyList());

    private final List<Frame> frames;
    /** Derived at first use; a String is safely published unsynchronized. */
    private String hash;
    private String rendered;

    private ExecutionIndex(List<Frame> frames) {
        this.frames = frames;
    }

    public static ExecutionIndex empty() {
        return EMPTY;
    }

    public static ExecutionIndex of(List<Frame> frames) {
        List<Frame> copied = Fields.copy(frames);
        return copied.isEmpty() ? EMPTY : new ExecutionIndex(copied);
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
        String folded = hash;
        if (folded == null) {
            folded = SEED;
            for (Frame frame : frames) folded = fold(folded, frame);
            hash = folded;
        }
        return folded;
    }

    public String render() {
        String text = rendered;
        if (text == null) {
            StringBuilder joined = new StringBuilder();
            for (Frame frame : frames) {
                if (joined.length() > 0) joined.append('/');
                joined.append(frame.render());
            }
            text = joined.toString();
            rendered = text;
        }
        return text;
    }

    /** The most folds {@link #FOLDS} holds before it starts over. */
    private static final int FOLDS_HELD = 1 << 14;

    /** Each fold by its SHA-256 input. */
    private static final Map<String, String> FOLDS =
            new ConcurrentHashMap<String, String>();

    private static String fold(String hash, Frame frame) {
        String input = hash + "/" + frame.callSite() + "@" + frame.iteration();
        String folded = FOLDS.get(input);
        if (folded == null) {
            folded = ArtifactIO.digest(input, 16);
            if (FOLDS.size() >= FOLDS_HELD) FOLDS.clear();
            FOLDS.put(input, folded);
        }
        return folded;
    }

    @Override
    Object[] parts() {
        return new Object[] {frames};
    }

    @Override
    public String toString() {
        return frames.isEmpty() ? "<no frames>" : render();
    }
}
