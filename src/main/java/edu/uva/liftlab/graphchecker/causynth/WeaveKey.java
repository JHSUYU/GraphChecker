package edu.uva.liftlab.graphchecker.causynth;

public final class WeaveKey {
    private WeaveKey() {
    }

    public static void main(String[] args) {
        System.out.println(
                ConcolicInstrumentationSelections.weaveKeyFromEnvironment());
    }
}
