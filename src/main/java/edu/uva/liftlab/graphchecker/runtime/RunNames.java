package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.RunSpellings;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * This run's names a node has only in it ({@link RunSpellings}, stated by
 * {@link MessageDoors#spelledAs}).  A location the schedule keys a write by
 * ({@code ScheduleEvent.Kind#WRITE}) states the node by its name, so the
 * recording and every replay key one path alike: a ZooKeeper leader
 * election's node is created under {@code <session id>-<core>-n_}, and the
 * session differs from run to run.  The session states them at its close
 * ({@code SessionManifest#runSpellings}).
 */
final class RunNames {
    private static volatile RunSpellings spellings = RunSpellings.NONE;

    private RunNames() {
    }

    /** The run-only names a location spelled that no adapter stated, each
     *  named once ({@link #firstUnstated}). */
    private static final Set<String> UNSTATED = new HashSet<String>();

    /** {@code spelling} is node {@code node}'s in this run ({@link
     *  RunSpellings#with}). */
    static synchronized void spelled(String node, String spelling) {
        spellings = spellings.with(node, spelling);
    }

    /** What one location keys as: each stated spelling named by its node,
     *  and the first run's own name no adapter stated, if any. */
    static final class Keyed {
        final String location;
        final String unnamed;

        private Keyed(String location, String unnamed) {
            this.location = location;
            this.unnamed = unnamed;
        }
    }

    static Keyed key(String location) {
        String keyed = spellings.name(location == null ? "" : location);
        return new Keyed(keyed, RunSpellings.unnamed(keyed));
    }

    /** Spelling -> node, every one stated so far. */
    static Map<String, String> stated() {
        return spellings.asMap();
    }

    /** Whether {@code unnamed} is named here for the first time. */
    static synchronized boolean firstUnstated(String unnamed) {
        return UNSTATED.add(unnamed);
    }

    static synchronized void resetForTests() {
        spellings = RunSpellings.NONE;
        UNSTATED.clear();
    }
}
