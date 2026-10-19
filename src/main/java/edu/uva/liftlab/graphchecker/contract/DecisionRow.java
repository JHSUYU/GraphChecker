package edu.uva.liftlab.graphchecker.contract;

import java.util.Map;

public final class DecisionRow extends Value {
    private final String sessionId;
    private final long seq;
    private final OccurrenceAddress occurrence;
    private final String siteId;
    private final int ordinal;
    private final boolean outcome;
    private final String term;
    private final Map<String, Long> clockReadings;
    private final Boolean concreteOutcome;
    private final String via;

    private DecisionRow(String sessionId, long seq,
                        OccurrenceAddress occurrence, String siteId,
                        int ordinal, boolean outcome, String term,
                        Map<String, Long> clockReadings,
                        Boolean concreteOutcome, String via) {
        this.sessionId = sessionId;
        this.seq = seq;
        this.occurrence = occurrence;
        this.siteId = siteId;
        this.ordinal = ordinal;
        this.outcome = outcome;
        this.term = term;
        this.clockReadings = clockReadings;
        this.concreteOutcome = concreteOutcome;
        this.via = via;
    }

    public static DecisionRow of(String sessionId, long seq,
                                 OccurrenceAddress occurrence, String siteId,
                                 int ordinal, boolean outcome, String term,
                                 Map<String, Long> clockReadings) {
        return new DecisionRow(Fields.text(sessionId, "sessionId"),
                Fields.nonNegative(seq, "seq"),
                Fields.required(occurrence, "occurrence"),
                Fields.text(siteId, "siteId"),
                Fields.ordinal(ordinal, "ordinal"), outcome,
                Fields.required(term, "term"), Fields.copy(clockReadings),
                null, "");
    }

    public DecisionRow forced(boolean concrete) {
        return new DecisionRow(sessionId, seq, occurrence, siteId, ordinal,
                outcome, term, clockReadings, Boolean.valueOf(concrete), via);
    }

    public DecisionRow via(String caller) {
        return new DecisionRow(sessionId, seq, occurrence, siteId, ordinal,
                outcome, term, clockReadings, concreteOutcome,
                caller == null ? "" : caller.trim());
    }

    public String via() {
        return via;
    }

    public boolean isForced() {
        return concreteOutcome != null;
    }

    public boolean concreteOutcome() {
        return concreteOutcome == null ? outcome
                : concreteOutcome.booleanValue();
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

    public String siteId() {
        return siteId;
    }

    public int ordinal() {
        return ordinal;
    }

    public boolean outcome() {
        return outcome;
    }

    public String term() {
        return term;
    }

    public Map<String, Long> clockReadings() {
        return clockReadings;
    }

    @Override
    Object[] parts() {
        return new Object[] {sessionId, seq, occurrence, siteId, ordinal,
                outcome, term, clockReadings, concreteOutcome, via};
    }

    @Override
    public String toString() {
        return "DecisionRow{" + sessionId + "#" + seq + " " + occurrence + " "
                + siteId + "#" + ordinal + "=" + outcome + "}";
    }
}
