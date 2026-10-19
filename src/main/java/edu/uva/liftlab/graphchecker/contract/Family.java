package edu.uva.liftlab.graphchecker.contract;

import java.util.List;

public final class Family extends Value {
    private final String interactionId;
    private final List<Arm> arms;

    private Family(String interactionId, List<Arm> arms) {
        this.interactionId = interactionId;
        this.arms = arms;
    }

    public static Family of(String interactionId, List<Arm> arms) {
        return new Family(Fields.text(interactionId, "interactionId"),
                Fields.copy(arms));
    }

    public String interactionId() {
        return interactionId;
    }

    public List<Arm> arms() {
        return arms;
    }

    @Override
    Object[] parts() {
        return new Object[] {interactionId, arms};
    }

    @Override
    public String toString() {
        return "Family{" + interactionId + " " + arms.size() + " arms}";
    }
}
