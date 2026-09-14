package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * CONTRACT-SPEC 3: one path prefix plus one flipped decision, with the
 * valuation that is supposed to produce it.
 *
 * <p>The runtime applies {@code rootAssignments} at the mints and
 * {@code answers} at the attaches of the focused occurrence -- keyed by attach
 * {@link Endpoint#id()}, because an answer belongs to one attach of one
 * occurrence and not to a port.  {@code unproducible} names the attaches whose
 * answer no producer arm can state; they are answered anyway and reported, so a
 * later stage refuses on named evidence rather than on a missing row.</p>
 */
public final class Obligation {
    private final String obligationId;
    private final String taskId;
    private final String pathId;
    private final String siteId;
    private final int ordinal;
    private final boolean flippedOutcome;
    private final Map<String, String> rootAssignments;
    private final Map<String, String> answers;
    private final List<String> unproducible;

    private Obligation(String obligationId, String taskId, String pathId,
                       String siteId, int ordinal, boolean flippedOutcome,
                       Map<String, String> rootAssignments,
                       Map<String, String> answers,
                       List<String> unproducible) {
        this.obligationId = obligationId;
        this.taskId = taskId;
        this.pathId = pathId;
        this.siteId = siteId;
        this.ordinal = ordinal;
        this.flippedOutcome = flippedOutcome;
        this.rootAssignments = rootAssignments;
        this.answers = answers;
        this.unproducible = unproducible;
    }

    public static Obligation of(String obligationId, String taskId,
                                String pathId, String siteId, int ordinal,
                                boolean flippedOutcome,
                                Map<String, String> rootAssignments,
                                Map<String, String> answers,
                                List<String> unproducible) {
        return new Obligation(Fields.text(obligationId, "obligationId"),
                Fields.text(taskId, "taskId"), Fields.text(pathId, "pathId"),
                Fields.text(siteId, "siteId"), Fields.ordinal(ordinal, "ordinal"),
                flippedOutcome, Fields.copy(rootAssignments),
                Fields.copy(answers), Fields.copy(unproducible));
    }

    public String obligationId() {
        return obligationId;
    }

    public String taskId() {
        return taskId;
    }

    /** The path whose prefix this obligation keeps. */
    public String pathId() {
        return pathId;
    }

    /** The decision site being flipped. */
    public String siteId() {
        return siteId;
    }

    /** The k-th decision of that site, 1-based. */
    public int ordinal() {
        return ordinal;
    }

    /** The arm the replay must take instead. */
    public boolean flippedOutcome() {
        return flippedOutcome;
    }

    /** Root symbol to value, applied at the mints. */
    public Map<String, String> rootAssignments() {
        return rootAssignments;
    }

    /** Attach {@link Endpoint#id()} to value, applied at the attaches. */
    public Map<String, String> answers() {
        return answers;
    }

    /** Attach endpoint ids answered without a producer arm. */
    public List<String> unproducible() {
        return unproducible;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof Obligation)) return false;
        Obligation other = (Obligation) value;
        return ordinal == other.ordinal
                && flippedOutcome == other.flippedOutcome
                && obligationId.equals(other.obligationId)
                && taskId.equals(other.taskId) && pathId.equals(other.pathId)
                && siteId.equals(other.siteId)
                && rootAssignments.equals(other.rootAssignments)
                && answers.equals(other.answers)
                && unproducible.equals(other.unproducible);
    }

    @Override
    public int hashCode() {
        return Objects.hash(obligationId, taskId, pathId, siteId, ordinal,
                flippedOutcome, rootAssignments, answers, unproducible);
    }

    @Override
    public String toString() {
        return "Obligation{" + obligationId + " " + siteId + "#" + ordinal
                + "->" + flippedOutcome + "}";
    }
}
