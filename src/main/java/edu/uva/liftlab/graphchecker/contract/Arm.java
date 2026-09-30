package edu.uva.liftlab.graphchecker.contract;

import java.util.Set;

/**
 * CONTRACT-SPEC §4: one producer path's arm of a family,
 * {@code pi_q and guard_q and v_H(I) = e_q}.  {@code guardRoots} is only the
 * roots {@code e_q} depends on, else unrelated arms contradict.
 * {@code attested} (IDENTITY §4): only a run with a recorded path
 * condition may carry a root move.
 */
public final class Arm extends Value {
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
                Fields.required(piRef, "piRef"),
                Fields.required(expressionRef, "expressionRef"),
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
    Object[] parts() {
        return new Object[] {producerPathId, piRef, expressionRef, guardRoots,
                attested};
    }

    @Override
    public String toString() {
        return "Arm{" + producerPathId + " -> " + expressionRef
                + (attested ? "}" : " unattested}");
    }
}
