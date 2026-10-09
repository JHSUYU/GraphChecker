package edu.uva.liftlab.graphchecker.contract;

import java.util.Collections;
import java.util.List;
import java.util.Map;

/**
 * CONTRACT-SPEC §3: one path prefix plus one flipped decision, with the
 * valuation meant to produce it: {@code rootAssignments} at the mints,
 * {@code answers} keyed by attach {@link Endpoint#id()} (one attach, not a
 * port).  {@code unproducible} attaches are answered anyway and reported.
 */
public final class Obligation extends Value {
    private final String obligationId;
    private final String taskId;
    private final String pathId;
    private final String siteId;
    private final int ordinal;
    private final boolean flippedOutcome;
    private final Map<String, String> rootAssignments;
    private final Map<String, String> answers;
    private final List<String> unproducible;
    /** A FORCE run ({@link #forcing}). */
    private final boolean force;

    private Obligation(String obligationId, String taskId, String pathId,
                       String siteId, int ordinal, boolean flippedOutcome,
                       Map<String, String> rootAssignments,
                       Map<String, String> answers,
                       List<String> unproducible, boolean force) {
        this.obligationId = obligationId;
        this.taskId = taskId;
        this.pathId = pathId;
        this.siteId = siteId;
        this.ordinal = ordinal;
        this.flippedOutcome = flippedOutcome;
        this.rootAssignments = rootAssignments;
        this.answers = answers;
        this.unproducible = unproducible;
        this.force = force;
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
                Fields.copy(answers), Fields.copy(unproducible), false);
    }

    /**
     * A CONFIRM run: plants a SAT model and holds the schedule but flips
     * nothing ({@link #flips()} false, empty site, ordinal 0).
     */
    public static Obligation confirming(String obligationId, String taskId,
                                        String pathId,
                                        Map<String, String> rootAssignments,
                                        Map<String, String> answers,
                                        List<String> unproducible) {
        return new Obligation(Fields.text(obligationId, "obligationId"),
                Fields.text(taskId, "taskId"), Fields.text(pathId, "pathId"),
                "", 0, false, Fields.copy(rootAssignments),
                Fields.copy(answers), Fields.copy(unproducible), false);
    }

    /**
     * A FORCE run (PIPELINE §7.10): the seed's world replayed with the
     * declared occurrence's branches forced to the throw; it flips nothing
     * and plants nothing.
     */
    public static Obligation forcing(String obligationId, String taskId,
                                     String pathId) {
        return new Obligation(Fields.text(obligationId, "obligationId"),
                Fields.text(taskId, "taskId"), Fields.text(pathId, "pathId"),
                "", 0, false, Collections.<String, String>emptyMap(),
                Collections.<String, String>emptyMap(),
                Collections.<String>emptyList(), true);
    }

    /** Whether this is a FORCE run ({@link #forcing}). */
    public boolean force() {
        return force;
    }

    /** Whether this obligation owes a decision the other arm at all. */
    public boolean flips() {
        return !siteId.isEmpty();
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
    Object[] parts() {
        return new Object[] {obligationId, taskId, pathId, siteId, ordinal,
                flippedOutcome, rootAssignments, answers, unproducible,
                force};
    }

    @Override
    public String toString() {
        return "Obligation{" + obligationId + (force ? " FORCE}"
                : " " + siteId + "#" + ordinal + "->" + flippedOutcome + "}");
    }
}
