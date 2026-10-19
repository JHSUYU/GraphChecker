package edu.uva.liftlab.graphchecker.contract;

public final class ObligationResult extends Value {
    public static final String WORLD_UNREFUTED = "WORLD_UNREFUTED";
    public static final String WORLD_RAN = "WORLD_RAN";
    public static final String ARM_REFUSED = "ARM_REFUSED";
    public static final String REPLAY_BOUNDED = "REPLAY_BOUNDED";

    private final String obligationId;
    private final Verdict verdict;
    private final String sessionId;
    private final String detail;
    private final WorldRefutation refutation;

    private ObligationResult(String obligationId, Verdict verdict,
                             String sessionId, String detail,
                             WorldRefutation refutation) {
        this.obligationId = obligationId;
        this.verdict = verdict;
        this.sessionId = sessionId;
        this.detail = detail;
        this.refutation = refutation;
    }

    public static ObligationResult of(String obligationId, Verdict verdict,
                                      String sessionId, String detail) {
        return of(obligationId, verdict, sessionId, detail, null);
    }

    public static ObligationResult of(String obligationId, Verdict verdict,
                                      String sessionId, String detail,
                                      WorldRefutation refutation) {
        if (refutation != null && verdict != Verdict.NOT_ADMITTED) {
            throw new IllegalArgumentException("only a NOT_ADMITTED verdict"
                    + " refutes its world; got " + verdict);
        }
        return new ObligationResult(Fields.text(obligationId, "obligationId"),
                Fields.required(verdict, "verdict"),
                Fields.required(sessionId, "sessionId"),
                Fields.required(detail, "detail"), refutation);
    }

    public String obligationId() {
        return obligationId;
    }

    public Verdict verdict() {
        return verdict;
    }

    public String sessionId() {
        return sessionId;
    }

    public String detail() {
        return detail;
    }

    public WorldRefutation refutation() {
        return refutation;
    }

    public boolean settlesArm() {
        return verdict == Verdict.ADMITTED || verdict == Verdict.UNSAT
                || verdict == Verdict.NOT_ADMITTED && refutation == null
                && (detail.startsWith(WORLD_RAN + ":")
                || detail.startsWith(ARM_REFUSED + ":"));
    }

    public boolean replayBounded() {
        return verdict == Verdict.NOT_ADMITTED
                && detail.startsWith(REPLAY_BOUNDED + ":");
    }

    public String armRefusal() {
        return verdict == Verdict.NOT_ADMITTED
                && detail.startsWith(ARM_REFUSED + ":")
                ? detail.substring(ARM_REFUSED.length() + 1).trim() : null;
    }

    public boolean worldUnrefuted() {
        return verdict == Verdict.NOT_ADMITTED && refutation == null
                && detail.startsWith(WORLD_UNREFUTED + ":");
    }

    @Override
    Object[] parts() {
        return new Object[] {obligationId, verdict, sessionId, detail,
                refutation};
    }

    @Override
    public String toString() {
        return "ObligationResult{" + obligationId + " " + verdict + "}";
    }
}
