package edu.uva.liftlab.graphchecker.contract;

import java.util.List;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

/**
 * CONTRACT-SPEC §3: why a replay's world is no world of its question
 * (WORLD_REFUTED).  An open decider arm's flip (TargetRow.OpenArm) whose
 * replay ran its world faithfully and never entered the flip's occurrence:
 * every assigned root and skew minted at its value and no prefix abandoned,
 * no order hold gave way (one still waiting at the end waits only on that
 * occurrence), the recorded order held until the world first acted, and the
 * workload ended by itself ({@code runtime.FocusedReplay#refuted}).
 * {@code conditions} states each as it held; {@code exception} the
 * workload's terminating throwable ("" when the method returned), {@code
 * thrownAt} its innermost frame and {@code testFrame} the test method's
 * frame it passed.  Never stated on CONFIRM's runs, nor on any other flip.
 */
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

    /** The faithfulness conditions (a)-(d), each as this run held it. */
    public List<String> conditions() {
        return conditions;
    }

    /** The workload's terminating throwable, or {@code ""}. */
    public String exception() {
        return exception;
    }

    /** Where it was thrown: its innermost frame, or {@code ""}. */
    public String thrownAt() {
        return thrownAt;
    }

    /** The test method's frame it passed through, or {@code ""}. */
    public String testFrame() {
        return testFrame;
    }

    @Override
    Object[] parts() {
        return new Object[] {conditions, exception, thrownAt, testFrame};
    }
}
