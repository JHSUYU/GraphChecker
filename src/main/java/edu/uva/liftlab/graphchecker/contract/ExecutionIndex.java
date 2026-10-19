package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public final class ExecutionIndex extends Value {
    private static final String SEED = ArtifactIO.digest("", 16);

    private static final ExecutionIndex EMPTY =
            new ExecutionIndex(Collections.<Frame>emptyList());

    private final List<Frame> frames;
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

    public List<Frame> frames() {
        return frames;
    }

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

    private static String fold(String hash, Frame frame) {
        return Digests.digest(hash + "/" + frame.callSite() + "@"
                + frame.iteration(), 16);
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
