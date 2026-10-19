package edu.uva.liftlab.graphchecker.contract;

import java.util.List;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

public final class WorldRefutation extends Value {
    private final List<String> conditions;
    private final String exception;
    private final String thrownAt;
    private final String testFrame;

    private WorldRefutation(List<String> conditions, String exception,
                            String thrownAt, String testFrame) {
        this.conditions = conditions;
        this.exception = exception;
        this.thrownAt = thrownAt;
        this.testFrame = testFrame;
    }

    public static WorldRefutation of(List<String> conditions,
                                     String exception, String thrownAt,
                                     String testFrame) {
        return new WorldRefutation(
                Fields.copy(Fields.required(conditions,
                        "refutation.conditions")),
                trimmed(exception), trimmed(thrownAt), trimmed(testFrame));
    }

    public List<String> conditions() {
        return conditions;
    }

    public String exception() {
        return exception;
    }

    public String thrownAt() {
        return thrownAt;
    }

    public String testFrame() {
        return testFrame;
    }

    @Override
    Object[] parts() {
        return new Object[] {conditions, exception, thrownAt, testFrame};
    }
}
