package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §3: what one obligation produced, and from which session.
 */
public final class ObligationResult extends Value {
    private final String obligationId;
    private final Verdict verdict;
    private final String sessionId;
    private final String detail;

    private ObligationResult(String obligationId, Verdict verdict,
                             String sessionId, String detail) {
        this.obligationId = obligationId;
        this.verdict = verdict;
        this.sessionId = sessionId;
        this.detail = detail;
    }

    public static ObligationResult of(String obligationId, Verdict verdict,
                                      String sessionId, String detail) {
        return new ObligationResult(Fields.text(obligationId, "obligationId"),
                Fields.required(verdict, "verdict"),
                Fields.required(sessionId, "sessionId"),
                Fields.required(detail, "detail"));
    }

    public String obligationId() {
        return obligationId;
    }

    public Verdict verdict() {
        return verdict;
    }

    /** The replay session that produced this result, or {@code ""}. */
    public String sessionId() {
        return sessionId;
    }

    public String detail() {
        return detail;
    }

    @Override
    Object[] parts() {
        return new Object[] {obligationId, verdict, sessionId, detail};
    }

    @Override
    public String toString() {
        return "ObligationResult{" + obligationId + " " + verdict + "}";
    }
}
