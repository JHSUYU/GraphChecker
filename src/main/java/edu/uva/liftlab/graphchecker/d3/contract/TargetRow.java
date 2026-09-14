package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 2: the anchor, as the runtime published it.
 *
 * <p>{@code phiTerm} is published in the FATAL polarity by the runtime and the
 * composer never re-derives it -- two places deciding a polarity is how a
 * composed formula ends up asserting the healthy arm and reporting the bug
 * as unsat.</p>
 */
public final class TargetRow {
    private final String sessionId;
    private final OccurrenceAddress occurrence;
    private final String anchorSiteId;
    private final String phiTerm;
    private final boolean observedFatal;
    private final boolean reachedAnchor;

    private TargetRow(String sessionId, OccurrenceAddress occurrence,
                      String anchorSiteId, String phiTerm,
                      boolean observedFatal, boolean reachedAnchor) {
        this.sessionId = sessionId;
        this.occurrence = occurrence;
        this.anchorSiteId = anchorSiteId;
        this.phiTerm = phiTerm;
        this.observedFatal = observedFatal;
        this.reachedAnchor = reachedAnchor;
    }

    public static TargetRow of(String sessionId, OccurrenceAddress occurrence,
                               String anchorSiteId, String phiTerm,
                               boolean observedFatal, boolean reachedAnchor) {
        return new TargetRow(Fields.text(sessionId, "sessionId"),
                Fields.required(occurrence, "occurrence"),
                Fields.text(anchorSiteId, "anchorSiteId"),
                Fields.stated(phiTerm, "phiTerm"), observedFatal,
                reachedAnchor);
    }

    public String sessionId() {
        return sessionId;
    }

    public OccurrenceAddress occurrence() {
        return occurrence;
    }

    /** The fatal read this anchor is about. */
    public String anchorSiteId() {
        return anchorSiteId;
    }

    /** phi, in the fatal polarity, as published. */
    public String phiTerm() {
        return phiTerm;
    }

    /** Whether this session observed the fatal arm. */
    public boolean observedFatal() {
        return observedFatal;
    }

    /** Whether this session reached the anchor at all. */
    public boolean reachedAnchor() {
        return reachedAnchor;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof TargetRow)) return false;
        TargetRow other = (TargetRow) value;
        return observedFatal == other.observedFatal
                && reachedAnchor == other.reachedAnchor
                && sessionId.equals(other.sessionId)
                && occurrence.equals(other.occurrence)
                && anchorSiteId.equals(other.anchorSiteId)
                && phiTerm.equals(other.phiTerm);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sessionId, occurrence, anchorSiteId, phiTerm,
                observedFatal, reachedAnchor);
    }

    @Override
    public String toString() {
        return "TargetRow{" + sessionId + " " + occurrence + " "
                + anchorSiteId + (observedFatal ? " fatal}" : "}");
    }
}
