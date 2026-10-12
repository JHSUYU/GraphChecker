package edu.uva.liftlab.graphchecker.contract;

import java.util.Map;

/**
 * CONTRACT-SPEC §2.2: one branch the focused region decided.  {@code
 * clockReadings} belong inside the path's own conjunction, never a global
 * assertion.  {@code seq} cuts a producer's path condition at its export, so a
 * consumer never conditions on a branch taken after the send.
 */
public final class DecisionRow extends Value {
    private final String sessionId;
    private final long seq;
    private final OccurrenceAddress occurrence;
    private final String siteId;
    private final int ordinal;
    private final boolean outcome;
    private final String term;
    private final Map<String, Long> clockReadings;
    /** The arm the run's operands decided where a forced replay forced
     *  another ({@link #forced}); null otherwise. */
    private final Boolean concreteOutcome;
    /** The frame that called the decision's method, where the anchor's
     *  forcing table names the site with a {@code via}; "" otherwise. */
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

    /**
     * This decision, FORCED (PIPELINE §7.10): the run took {@code outcome}
     * because the replay forced it, where its operands decided {@code
     * concrete}; {@code term} is the predicate as written, as for any row.
     */
    public DecisionRow forced(boolean concrete) {
        return new DecisionRow(sessionId, seq, occurrence, siteId, ordinal,
                outcome, term, clockReadings, Boolean.valueOf(concrete), via);
    }

    /**
     * This decision, made in a call from {@code caller} (a frame as {@code
     * runtime.Identity#callerFrame} names it): stated where the occurrence's
     * forcing table names the site with a {@code via}, a decider counting
     * only in a call of its helper from there ({@code
     * compose.RestsOn#wayGuard}).
     */
    public DecisionRow via(String caller) {
        return new DecisionRow(sessionId, seq, occurrence, siteId, ordinal,
                outcome, term, clockReadings, concreteOutcome,
                caller == null ? "" : caller.trim());
    }

    /** The frame that called it, or "" where none was stated. */
    public String via() {
        return via;
    }

    /** Whether a forced replay forced this decision. */
    public boolean isForced() {
        return concreteOutcome != null;
    }

    /** The arm its operands decided: {@link #outcome} unless forced. */
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

    /** The branch site inside the region. */
    public String siteId() {
        return siteId;
    }

    /** The k-th decision of that site inside this occurrence, 1-based. */
    public int ordinal() {
        return ordinal;
    }

    /** The arm the run took. */
    public boolean outcome() {
        return outcome;
    }

    /** The predicate in SMT-LIB over the declared symbols. */
    public String term() {
        return term;
    }

    /** The clocks read while deciding, by solver symbol. */
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
