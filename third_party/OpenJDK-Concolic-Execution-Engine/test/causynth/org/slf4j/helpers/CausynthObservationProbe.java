package org.slf4j.helpers;

/** A smoke-only logging implementation whose body must remain concrete. */
public final class CausynthObservationProbe {
    private CausynthObservationProbe() {
    }

    public static int format(int value) {
        int total = 0;
        for (int index = 0; index < 512; index++) {
            int[] arguments = {value, index};
            if (arguments[0] >= 0) {
                total += arguments[1];
            }
        }
        return total;
    }
}
