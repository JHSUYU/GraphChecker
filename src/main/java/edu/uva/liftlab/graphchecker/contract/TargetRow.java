package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC 2: the anchor, as the runtime published it.  {@code phiTerm}
 * is in the FATAL polarity and the composer never re-derives it: two places
 * deciding polarity end up asserting the healthy arm.
 */
public final class TargetRow extends Value {
    private final String sessionId;
    private final long seq;
    private final OccurrenceAddress occurrence;
    private final String anchorSiteId;
    private final String phiTerm;
    private final boolean observedFatal;
    private final boolean reachedAnchor;

    private TargetRow(String sessionId, long seq, OccurrenceAddress occurrence,
                      String anchorSiteId, String phiTerm,
                      boolean observedFatal, boolean reachedAnchor) {
        this.sessionId = sessionId;
        this.seq = seq;
        this.occurrence = occurrence;
        this.anchorSiteId = anchorSiteId;
        this.phiTerm = phiTerm;
        this.observedFatal = observedFatal;
        this.reachedAnchor = reachedAnchor;
    }

    public static TargetRow of(String sessionId, long seq,
                               OccurrenceAddress occurrence,
                               String anchorSiteId, String phiTerm,
                               boolean observedFatal, boolean reachedAnchor) {
        return new TargetRow(Fields.text(sessionId, "sessionId"),
                Fields.nonNegative(seq, "seq"),
                Fields.required(occurrence, "occurrence"),
                Fields.text(anchorSiteId, "anchorSiteId"),
                Fields.required(phiTerm, "phiTerm"), observedFatal,
                reachedAnchor);
    }

    public String sessionId() {
        return sessionId;
    }

    public long seq() {
        return seq;
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
    Object[] parts() {
        return new Object[] {sessionId, seq, occurrence, anchorSiteId, phiTerm,
                observedFatal, reachedAnchor};
    }

    @Override
    public String toString() {
        return "TargetRow{" + sessionId + "#" + seq + " " + occurrence + " "
                + anchorSiteId + (observedFatal ? " fatal}" : "}");
    }
}
