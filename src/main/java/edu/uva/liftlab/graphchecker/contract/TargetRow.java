package edu.uva.liftlab.graphchecker.contract;

public final class TargetRow extends Value {
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

        public static OpenArm of(String siteId, int ordinal, boolean outcome,
                                 String askedSiteId, int askedOrdinal) {
            String asked = askedSiteId == null ? "" : askedSiteId.trim();
            return new OpenArm(Fields.text(siteId, "openArm.siteId"),
                    Fields.ordinal(ordinal, "openArm.ordinal"), outcome,
                    asked, asked.isEmpty() ? 0
                            : Fields.ordinal(askedOrdinal,
                            "openArm.askedOrdinal"));
        }

        public String siteId() {
            return siteId;
        }

        public int ordinal() {
            return ordinal;
        }

        public boolean outcome() {
            return outcome;
        }

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
    private final OpenArm openArm;
    private final boolean forced;

    private TargetRow(String sessionId, long seq, OccurrenceAddress occurrence,
                      String anchorSiteId, String phiTerm,
                      boolean observedFatal, boolean reachedAnchor,
                      OpenArm openArm, boolean forced) {
        this.sessionId = sessionId;
        this.seq = seq;
        this.occurrence = occurrence;
        this.anchorSiteId = anchorSiteId;
        this.phiTerm = phiTerm;
        this.observedFatal = observedFatal;
        this.reachedAnchor = reachedAnchor;
        this.openArm = openArm;
        this.forced = forced;
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
                reachedAnchor, openArm, false);
    }

    public TargetRow forced() {
        return new TargetRow(sessionId, seq, occurrence, anchorSiteId,
                phiTerm, false, reachedAnchor, openArm, true);
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

    public String anchorSiteId() {
        return anchorSiteId;
    }

    public String site() {
        int hash = anchorSiteId.lastIndexOf('#');
        if (hash <= 0 || hash == anchorSiteId.length() - 1) {
            return anchorSiteId;
        }
        for (int at = hash + 1; at < anchorSiteId.length(); at++) {
            if (!Character.isDigit(anchorSiteId.charAt(at))) {
                return anchorSiteId;
            }
        }
        return anchorSiteId.substring(0, hash);
    }

    public String phiTerm() {
        return phiTerm;
    }

    public boolean observedFatal() {
        return observedFatal;
    }

    public boolean reachedAnchor() {
        return reachedAnchor;
    }

    public OpenArm openArm() {
        return openArm;
    }

    public boolean isForced() {
        return forced;
    }

    @Override
    Object[] parts() {
        return new Object[] {sessionId, seq, occurrence, anchorSiteId, phiTerm,
                observedFatal, reachedAnchor, openArm, forced};
    }

    @Override
    public String toString() {
        return "TargetRow{" + sessionId + "#" + seq + " " + occurrence + " "
                + anchorSiteId + (observedFatal ? " fatal" : "")
                + (forced ? " forced}" : "}");
    }
}
