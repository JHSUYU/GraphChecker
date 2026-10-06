package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §2.2: the anchor, as the runtime published it.  {@code phiTerm}
 * is in the FATAL polarity and the composer never re-derives it: two places
 * deciding polarity end up asserting the healthy arm.
 */
public final class TargetRow extends Value {
    /**
     * The arm of the helper decision that chose what a reached target tested
     * when this run took its constant sibling and the arm itself is OPEN
     * (causynth.BooleanReturns): it runs on to a value no constant states,
     * so phi states nothing of it.  {@code asked} is the decision whose flip
     * runs it -- the decision itself where it states a predicate, else the
     * nested helper decision its condition rests on -- or empty where none
     * does (a concrete decision over nothing that moves).
     */
    public static final class OpenArm extends Value {
        private final String siteId;
        private final int ordinal;
        private final boolean outcome;
        private final String askedSiteId;
        private final int askedOrdinal;

        private OpenArm(String siteId, int ordinal, boolean outcome,
                        String askedSiteId, int askedOrdinal) {
            this.siteId = siteId;
            this.ordinal = ordinal;
            this.outcome = outcome;
            this.askedSiteId = askedSiteId;
            this.askedOrdinal = askedOrdinal;
        }

        /** {@code askedSiteId} empty: no decision's flip runs the arm. */
        public static OpenArm of(String siteId, int ordinal, boolean outcome,
                                 String askedSiteId, int askedOrdinal) {
            String asked = askedSiteId == null ? "" : askedSiteId.trim();
            return new OpenArm(Fields.text(siteId, "openArm.siteId"),
                    Fields.ordinal(ordinal, "openArm.ordinal"), outcome,
                    asked, asked.isEmpty() ? 0
                            : Fields.ordinal(askedOrdinal,
                            "openArm.askedOrdinal"));
        }

        /** The deciding branch. */
        public String siteId() {
            return siteId;
        }

        /** Its decision's ordinal in the occurrence. */
        public int ordinal() {
            return ordinal;
        }

        /** The open arm: the outcome this run did not take. */
        public boolean outcome() {
            return outcome;
        }

        /** The decision whose flip runs the arm, or {@code ""}. */
        public String askedSiteId() {
            return askedSiteId;
        }

        public int askedOrdinal() {
            return askedOrdinal;
        }

        @Override
        Object[] parts() {
            return new Object[] {siteId, ordinal, outcome, askedSiteId,
                    askedOrdinal};
        }

        @Override
        public String toString() {
            return siteId + "#" + ordinal + "=" + outcome
                    + (askedSiteId.isEmpty() ? ""
                    : " asked at " + askedSiteId + "#" + askedOrdinal);
        }
    }

    private final String sessionId;
    private final long seq;
    private final OccurrenceAddress occurrence;
    private final String anchorSiteId;
    private final String phiTerm;
    private final boolean observedFatal;
    private final boolean reachedAnchor;
    /** Null unless phi left an open decider arm out ({@link OpenArm}). */
    private final OpenArm openArm;

    private TargetRow(String sessionId, long seq, OccurrenceAddress occurrence,
                      String anchorSiteId, String phiTerm,
                      boolean observedFatal, boolean reachedAnchor,
                      OpenArm openArm) {
        this.sessionId = sessionId;
        this.seq = seq;
        this.occurrence = occurrence;
        this.anchorSiteId = anchorSiteId;
        this.phiTerm = phiTerm;
        this.observedFatal = observedFatal;
        this.reachedAnchor = reachedAnchor;
        this.openArm = openArm;
    }

    public static TargetRow of(String sessionId, long seq,
                               OccurrenceAddress occurrence,
                               String anchorSiteId, String phiTerm,
                               boolean observedFatal, boolean reachedAnchor) {
        return of(sessionId, seq, occurrence, anchorSiteId, phiTerm,
                observedFatal, reachedAnchor, null);
    }

    public static TargetRow of(String sessionId, long seq,
                               OccurrenceAddress occurrence,
                               String anchorSiteId, String phiTerm,
                               boolean observedFatal, boolean reachedAnchor,
                               OpenArm openArm) {
        return new TargetRow(Fields.text(sessionId, "sessionId"),
                Fields.nonNegative(seq, "seq"),
                Fields.required(occurrence, "occurrence"),
                Fields.text(anchorSiteId, "anchorSiteId"),
                Fields.required(phiTerm, "phiTerm"), observedFatal,
                reachedAnchor, openArm);
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

    /** The open decider arm phi left out, or null. */
    public OpenArm openArm() {
        return openArm;
    }

    @Override
    Object[] parts() {
        return new Object[] {sessionId, seq, occurrence, anchorSiteId, phiTerm,
                observedFatal, reachedAnchor, openArm};
    }

    @Override
    public String toString() {
        return "TargetRow{" + sessionId + "#" + seq + " " + occurrence + " "
                + anchorSiteId + (observedFatal ? " fatal}" : "}");
    }
}
