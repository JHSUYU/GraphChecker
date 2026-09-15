package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;
import java.util.Set;

/**
 * CONTRACT-SPEC 4: one producer path's contribution to a family.
 *
 * <p>{@code pi_q and guard_q and v_H(I) = e_q}: {@code piRef} names the
 * producer path's condition, {@code expressionRef} the value it would export,
 * and {@code guardRoots} ONLY the roots {@code e_q} depends on -- a guard over
 * every root of the producer's run would make one arm contradict another for
 * reasons the exported value does not depend on.</p>
 *
 * <p>{@code attested} is INTERACTION-ID R-I5: an arm from a run that recorded
 * a path condition may carry a root move; an arm from a run that only ran
 * concretely states what was delivered and no more.</p>
 */
public final class Arm {
    private final String producerPathId;
    private final String piRef;
    private final String expressionRef;
    private final Set<String> guardRoots;
    private final boolean attested;

    private Arm(String producerPathId, String piRef, String expressionRef,
                Set<String> guardRoots, boolean attested) {
        this.producerPathId = producerPathId;
        this.piRef = piRef;
        this.expressionRef = expressionRef;
        this.guardRoots = guardRoots;
        this.attested = attested;
    }

    public static Arm of(String producerPathId, String piRef,
                         String expressionRef, Set<String> guardRoots,
                         boolean attested) {
        return new Arm(Fields.text(producerPathId, "producerPathId"),
                Fields.stated(piRef, "piRef"),
                Fields.stated(expressionRef, "expressionRef"),
                Fields.copy(guardRoots), attested);
    }

    /** The exported value {@code e_q}. */
    public String expressionRef() {
        return expressionRef;
    }

    /** Only the roots {@code e_q} depends on. */
    public Set<String> guardRoots() {
        return guardRoots;
    }

    /** Whether the producer run recorded a path condition. */
    public boolean attested() {
        return attested;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof Arm)) return false;
        Arm other = (Arm) value;
        return attested == other.attested
                && producerPathId.equals(other.producerPathId)
                && piRef.equals(other.piRef)
                && expressionRef.equals(other.expressionRef)
                && guardRoots.equals(other.guardRoots);
    }

    @Override
    public int hashCode() {
        return Objects.hash(producerPathId, piRef, expressionRef, guardRoots,
                attested);
    }

    @Override
    public String toString() {
        return "Arm{" + producerPathId + " -> " + expressionRef
                + (attested ? "}" : " unattested}");
    }
}
