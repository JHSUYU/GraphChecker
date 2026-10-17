package edu.uva.liftlab.graphchecker.causynth;

/**
 * Prints the weave key of the plan this JVM is given as the weave is
 * ({@code -Dcausynth.concolic.task.plan}, {@code .task.id}, {@code
 * .campaign.max.tasks}; {@link
 * ConcolicInstrumentationSelections#weaveKeyFromEnvironment}): run_engine.sh
 * campaign_weave_key.
 */
public final class WeaveKey {
    private WeaveKey() {
    }

    public static void main(String[] args) {
        System.out.println(
                ConcolicInstrumentationSelections.weaveKeyFromEnvironment());
    }
}
