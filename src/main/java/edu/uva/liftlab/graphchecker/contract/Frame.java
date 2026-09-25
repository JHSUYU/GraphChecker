package edu.uva.liftlab.graphchecker.contract;

import java.util.Objects;

/**
 * IDENTITY-IMPL A: one execution-index frame -- static {@code callSite}
 * ({@code class#method#bci}) and {@code iteration}, the k-th entry of that
 * site in the enclosing frame ({@code runtime.Identity}).  A call site
 * carries neither {@code /} nor {@code @}, so an index parses back exactly.
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

    /** The k-th entry of this site in the enclosing frame, from 0. */
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
