package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §3: what one obligation produced, and from which session.  A
 * NOT_ADMITTED open-arm flip whose replay refuted its world states why
 * ({@link WorldRefutation}): its arm stays owed, asked again without that
 * world ({@code explore.Frontier#consume}).  One whose replay did not run
 * its world faithfully says so first ({@link #WORLD_UNREFUTED}): it is asked
 * once more.
 */
public final class ObligationResult extends Value {
    /** How a NOT_ADMITTED open-arm flip's detail opens when its replay never
     *  reached the decision and did not run its world faithfully either
     *  ({@code runtime.FocusedReplay#refuted}'s conditions failed). */
    public static final String WORLD_UNREFUTED = "WORLD_UNREFUTED";

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

    /** {@code refutation} null unless the verdict is a NOT_ADMITTED that
     *  refuted its world. */
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

    /** The replay session that produced this result, or {@code ""}. */
    public String sessionId() {
        return sessionId;
    }

    public String detail() {
        return detail;
    }

    /** Why the replay refuted its world, or null. */
    public WorldRefutation refutation() {
        return refutation;
    }

    /** Whether this is an open-arm flip's replay that ran its world neither
     *  into the decision nor faithfully ({@link #WORLD_UNREFUTED}). */
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
