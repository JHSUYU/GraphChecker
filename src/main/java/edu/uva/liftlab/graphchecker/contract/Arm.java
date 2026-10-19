package edu.uva.liftlab.graphchecker.contract;

import java.util.Set;

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

    public Set<String> guardRoots() {
        return guardRoots;
    }

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
