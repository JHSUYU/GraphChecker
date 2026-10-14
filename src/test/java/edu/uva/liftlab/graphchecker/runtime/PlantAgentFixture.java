package edu.uva.liftlab.graphchecker.runtime;

/** A class the plant-run agent rewrites
 *  ({@link RecordingPlantTest#namedInvokesHandTheirReturnsToThePlant}): calls
 *  of each return type, one before a branch (a frame after the call). */
public final class PlantAgentFixture {
    private PlantAgentFixture() {
    }

    public static long clock(boolean later) {
        long now = System.currentTimeMillis();
        if (later) {
            now = now + 1L;
        }
        return now;
    }

    public static int parsed(String text) {
        return Integer.parseInt(text);
    }

    public static String[] split(String text) {
        return text.split(",");
    }

    public static String named(Object value) {
        return String.valueOf(value);
    }

    public static void collected() {
        System.gc();
    }
}
