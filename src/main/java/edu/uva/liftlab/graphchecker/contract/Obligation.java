package edu.uva.liftlab.graphchecker.contract;

import java.util.Collections;
import java.util.List;
import java.util.Map;

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

    public static Obligation forcing(String obligationId, String taskId,
                                     String pathId) {
        return new Obligation(Fields.text(obligationId, "obligationId"),
                Fields.text(taskId, "taskId"), Fields.text(pathId, "pathId"),
                "", 0, false, Collections.<String, String>emptyMap(),
                Collections.<String, String>emptyMap(),
                Collections.<String>emptyList(), true);
    }

    public boolean force() {
        return force;
    }

    public boolean flips() {
        return !siteId.isEmpty();
    }

    public static final String PAIRING = "PAIRING:";

    public static boolean pairing(String siteId) {
        return siteId != null && siteId.startsWith(PAIRING);
    }

    public boolean pairing() {
        return pairing(siteId);
    }

    public long pairedVersion() {
        return ordinal - 1L;
    }

    public String pairedReader() {
        return pairing() ? siteId.substring(PAIRING.length()) : "";
    }

    public String obligationId() {
        return obligationId;
    }

    public String taskId() {
        return taskId;
    }

    public String pathId() {
        return pathId;
    }

    public String siteId() {
        return siteId;
    }

    public int ordinal() {
        return ordinal;
    }

    public boolean flippedOutcome() {
        return flippedOutcome;
    }

    public Map<String, String> rootAssignments() {
        return rootAssignments;
    }

    public Map<String, String> answers() {
        return answers;
    }

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
