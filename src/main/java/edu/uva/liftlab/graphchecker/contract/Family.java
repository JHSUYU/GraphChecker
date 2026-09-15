package edu.uva.liftlab.graphchecker.contract;

import java.util.List;
import java.util.Objects;

/**
 * CONTRACT-SPEC 4: everything one interaction's control could have carried.
 *
 * <p>Keyed by the interaction id -- BOTH endpoints -- and never by the consumer
 * phase: a producer path with the same port but another endpoint contributes
 * nothing here (INTERACTION-ID R-I2).  A family with no arm is a control
 * nothing in the corpus can produce, which is a row to report, not a
 * disjunction to invent.</p>
 */
public final class Family {
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
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof Family)) return false;
        Family other = (Family) value;
        return interactionId.equals(other.interactionId)
                && arms.equals(other.arms);
    }

    @Override
    public int hashCode() {
        return Objects.hash(interactionId, arms);
    }

    @Override
    public String toString() {
        return "Family{" + interactionId + " " + arms.size() + " arms}";
    }
}
