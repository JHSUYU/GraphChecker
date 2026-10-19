package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import java.util.function.Predicate;

public final class Sessions {
    private static volatile Predicate<Object> expirer;

    private Sessions() {
    }

    public static void expirer(Predicate<Object> expires) {
        expirer = expires;
    }

    public static boolean expires(Object owner, String marker) {
        String refused;
        try {
            Predicate<Object> expires = expirer;
            if (expires == null) {
                refused = "no system expirer is registered (no in-process"
                        + " ZooKeeper server the cluster harness names)";
            } else if (expire(expires, owner)) {
                return true;
            } else {
                refused = "the system's expirer knows no session of "
                        + (owner == null ? "a static door"
                        : owner.getClass().getName());
            }
        } catch (RuntimeException failed) {
            refused = "the system's expirer failed: " + failed;
        }
        if (!RecordingPlant.plantRefused(marker, refused)) {
            ActiveRegion active = ConcolicRegionRuntime.activeRegion();
            RowRuntime.gap(GapKind.ASSIGNMENT_UNPLANTED, GapClass.BLOCKING,
                    marker + (active == null ? "" : " at "
                            + active.address()), "the planted session"
                            + " expiry cannot happen: " + refused
                            + ", so the call's own result stood");
        }
        return false;
    }

    private static boolean expire(Predicate<Object> expires, Object owner) {
        ConcolicRegionRuntime.pauseObservation();
        try {
            return expires.test(owner);
        } finally {
            ConcolicRegionRuntime.resumeObservation();
        }
    }
}
