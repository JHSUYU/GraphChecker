package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import java.util.function.Predicate;

/**
 * A PLANTED SESSIONEXPIRED IS A REAL EXPIRY.  ZooKeeper expires a session at
 * its server: the server deletes the session's ephemeral nodes (an Overseer's
 * leader node, a node's live_nodes entry, its election nodes), every later
 * operation on that handle fails by itself, and the client makes a new
 * session and re-registers.  An exception planted on one operation of a live
 * session reaches a world none of that happens in: Solr's Overseer catches a
 * SessionExpired and exits its loop, while its node's session -- and with it
 * the leader node no other node may take -- lives on
 * (solr-bugs-overseer-lock-leak LL4).  So a SessionExpired door's fault arm
 * asks here first ({@code causynth.DoorWeave#guard}): the system's expirer
 * expires the session of the door's owner at its server, and only then does
 * the door throw; everything after is the system's own handling.  CONFIRM
 * and a native run plant through the same arm.
 */
public final class Sessions {
    /**
     * The system's expirer: given a door's owner (the client whose method
     * holds the door), expires its session at the server and answers true
     * once the server closed it; false when it knows no session of it.
     * Registered by the system's cluster harness (Solr's
     * {@code CausynthSolrCluster}, over its in-process ZooKeeper server).
     */
    private static volatile Predicate<Object> expirer;

    private Sessions() {
    }

    /** Registers the system's expirer ({@link #expirer}); the last one
     *  stands. */
    public static void expirer(Predicate<Object> expires) {
        expirer = expires;
    }

    /**
     * Whether the planted SessionExpired of {@code marker} is real: true once
     * the session of {@code owner} expired at its server.  A world the run
     * cannot reach that way is refused by name where it is planted -- a
     * native run states its FAULT row unwritten, a replay an
     * ASSIGNMENT_UNPLANTED row, which CONFIRM refutes -- and the call's own
     * result stands.
     */
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

    /** The expirer run as engine work: the system's harness and its
     *  in-process server never reach the workload's path condition. */
    private static boolean expire(Predicate<Object> expires, Object owner) {
        ConcolicRegionRuntime.pauseObservation();
        try {
            return expires.test(owner);
        } finally {
            ConcolicRegionRuntime.resumeObservation();
        }
    }

    static void resetForTests() {
        expirer = null;
    }
}
