package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * IDENTITY-IMPL A: one frame of an execution index.
 *
 * <p>{@code callSite} is the static call site ({@code class#method#bci}) and
 * {@code iteration} the innermost enclosing loop's iteration count at that
 * frame (0 when the frame is not inside a loop).  This is the Execution
 * Indexing / PEPID form: a point is named by its dynamic control context, so an
 * unrelated extra call elsewhere does not move it while an extra iteration of a
 * loop ON the path does -- which is inherent, and what makes the occurrences
 * of two replays correspond.</p>
 *
 * <p>A call site carries neither {@code /} nor {@code @}, the two separators of
 * the canonical render, so an index parses back exactly as it was written.</p>
 */
public final class Frame {
    private final String callSite;
    private final int iteration;

    private Frame(String callSite, int iteration) {
        this.callSite = callSite;
        this.iteration = iteration;
    }

    public static Frame of(String callSite, int iteration) {
        String site = Fields.text(callSite, "callSite");
        if (site.indexOf('/') >= 0 || site.indexOf('@') >= 0) {
            throw new IllegalArgumentException(
                    "a call site carries no '/' or '@': " + callSite);
        }
        return new Frame(site, Fields.count(iteration, "iteration"));
    }

    /** Reads {@code <callSite>@<iteration>}. */
    public static Frame parse(String rendered) {
        String value = rendered == null ? "" : rendered.trim();
        int marker = value.lastIndexOf('@');
        if (marker <= 0 || marker + 1 >= value.length()) {
            throw new IllegalArgumentException(
                    "not a <callSite>@<iteration>: " + rendered);
        }
        String iteration = value.substring(marker + 1);
        for (int index = 0; index < iteration.length(); index++) {
            if (!Character.isDigit(iteration.charAt(index))) {
                throw new IllegalArgumentException(
                        "not a <callSite>@<iteration>: " + rendered);
            }
        }
        return of(value.substring(0, marker), Integer.parseInt(iteration));
    }

    /** The static call site: {@code class#method#bci}. */
    public String callSite() {
        return callSite;
    }

    /** The innermost enclosing loop's iteration, 0 outside a loop. */
    public int iteration() {
        return iteration;
    }

    public String render() {
        return callSite + "@" + iteration;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof Frame)) return false;
        Frame other = (Frame) value;
        return iteration == other.iteration && callSite.equals(other.callSite);
    }

    @Override
    public int hashCode() {
        return Objects.hash(callSite, iteration);
    }

    @Override
    public String toString() {
        return render();
    }
}
