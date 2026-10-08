package edu.uva.liftlab.graphchecker.runtime;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * The names a node has only in this run -- the id of its store session, its
 * host and port -- each standing for the node's own name, its registered
 * source ({@link MessageDoors#spelledAs}).  A location the schedule keys a
 * write by ({@code ScheduleEvent.Kind#WRITE}) states the node by that name,
 * so the recording and every replay key one path alike: a ZooKeeper leader
 * election's node is created under {@code <session id>-<core>-n_}, and the
 * session differs from run to run.
 */
final class RunNames {
    /** What still spells a run's own name once the stated ones are named:
     *  a long number (a session id, a time) or a host and port. */
    private static final Pattern UNNAMED = Pattern.compile(
            "\\d{13,}|\\d{1,3}(?:\\.\\d{1,3}){3}:\\d+");

    /** Spelling and node, the longest spelling first (a host:port inside a
     *  longer one is named as part of it). */
    private static volatile List<String[]> spellings =
            Collections.emptyList();

    private RunNames() {
    }

    /** The run-only names a location spelled that no adapter stated, each
     *  named once ({@link #firstUnstated}). */
    private static final Set<String> UNSTATED = new HashSet<String>();

    /**
     * {@code spelling} is node {@code node}'s in this run.  Only a spelling
     * that holds a run-only name ({@link #UNNAMED}) is one: a session not yet
     * connected spells {@code 0}, which would rename every 0.  Stated again
     * (a restarted node, a renewed session) it is kept once.
     */
    static synchronized void spelled(String node, String spelling) {
        if (spelling == null || node == null || node.isEmpty()
                || !UNNAMED.matcher(spelling).find()) {
            return;
        }
        for (String[] named : spellings) {
            if (named[0].equals(spelling)) return;
        }
        List<String[]> next = new ArrayList<String[]>(spellings);
        next.add(new String[] {spelling, "{" + node + "}"});
        next.sort(Comparator.comparingInt(
                (String[] named) -> named[0].length()).reversed());
        spellings = Collections.unmodifiableList(next);
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
        String keyed = location == null ? "" : location;
        for (String[] named : spellings) {
            keyed = keyed.replace(named[0], named[1]);
        }
        Matcher left = UNNAMED.matcher(keyed);
        return new Keyed(keyed, left.find() ? left.group() : "");
    }

    /** Whether {@code unnamed} is named here for the first time. */
    static synchronized boolean firstUnstated(String unnamed) {
        return UNSTATED.add(unnamed);
    }

    static synchronized void resetForTests() {
        spellings = Collections.emptyList();
        UNSTATED.clear();
    }
}
