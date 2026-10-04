package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * THE order nodes pass a startup step an adapter names: a step that builds
 * state a replay reads, taken before the window, where no slot of the
 * schedule holds it (IDENTITY §8).  HDFS's is a DataNode's
 * {@code registerDatanode}: the NameNode adds the DataNodes to its
 * NetworkTopology in that order, and block placement picks a pipeline by
 * position in it, so a replay whose DataNodes registered in another order
 * wrote its blocks to other nodes though it drew what its recording drew
 * (hdfs-adhoc-01/43, STATUS open defect 40).
 *
 * <p>The recording states each completion as a {@code STARTUP} mark of its
 * schedule (step, node), in completion order, handed on with every order
 * ({@code explore.SchedulePrefix}).  A replay holds a node at the step until
 * every node marked before it there has completed it, a node's n-th pass
 * standing for its n-th mark; at most one schedule timeout, after which the
 * missing nodes are given up by name ({@code SCHEDULE_DIVERGED}).</p>
 */
public final class StartupOrder {
    private static final Object LOCK = new Object();
    /** Per step, the passes the order handed to this replay marks, in their
     *  order ({@code node#n}); read once. */
    private static Map<String, List<String>> marked;
    /** Per step, the passes completed in this run, or given up. */
    private static final Map<String, Set<String>> PASSED =
            new HashMap<String, Set<String>>();
    /** Per step and node, how often it began the step in this run. */
    private static final Map<String, Integer> BEGUN =
            new HashMap<String, Integer>();

    private StartupOrder() {
    }

    /**
     * {@code node} is about to take {@code step}: in a replay, held until the
     * passes marked before its own completed.
     *
     * @return what {@link #done} takes, or null when nothing is named
     */
    static String[] begin(String step, String node) {
        String named = Text.safe(step);
        String by = Text.safe(node);
        if (named.isEmpty() || by.isEmpty()) return null;
        synchronized (LOCK) {
            int n = BEGUN.merge(named + "\n" + by, 1, Integer::sum) - 1;
            String pass = by + "#" + n;
            List<String> order = markedLocked().get(named);
            int at = order == null ? -1 : order.indexOf(pass);
            Set<String> passed = passedLocked(named);
            List<String> before = at <= 0 ? new ArrayList<String>()
                    : new ArrayList<String>(order.subList(0, at));
            long deadline = System.currentTimeMillis()
                    + ScheduleLog.timeoutMillis();
            while (!passed.containsAll(before)) {
                long left = deadline - System.currentTimeMillis();
                if (left <= 0L) {
                    before.removeAll(passed);
                    passed.addAll(before);
                    ScheduleLog.diverged("startup#" + named, pass + " took "
                            + named + " after waiting "
                            + ScheduleLog.timeoutMillis() + " ms for " + before
                            + ", marked before it, which did not complete it:"
                            + " they are given up");
                    break;
                }
                try {
                    LOCK.wait(left);
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                    break;
                }
            }
            return new String[] {named, pass};
        }
    }

    /** The pass {@link #begin} returned completed: marked, and the nodes
     *  held behind it go on. */
    static void done(String[] pass) {
        if (pass == null) return;
        synchronized (LOCK) {
            passedLocked(pass[0]).add(pass[1]);
            LOCK.notifyAll();
        }
        String node = pass[1].substring(0, pass[1].lastIndexOf('#'));
        ScheduleLog.writeMark(RowCodec.writeScheduleStartup(pass[0], node));
    }

    private static Set<String> passedLocked(String step) {
        return PASSED.computeIfAbsent(step, ignored -> new HashSet<String>());
    }

    private static Map<String, List<String>> markedLocked() {
        if (marked == null) {
            marked = new HashMap<String, List<String>>();
            Map<String, Integer> passes = new HashMap<String, Integer>();
            for (JsonObject mark : ScheduleLog.startupMarks()) {
                String step = mark.get("step").getAsString();
                String node = mark.get("node").getAsString();
                int n = passes.merge(step + "\n" + node, 1, Integer::sum) - 1;
                marked.computeIfAbsent(step, ignored -> new ArrayList<String>())
                        .add(node + "#" + n);
            }
        }
        return marked;
    }

    /** Test seam: a fresh run. */
    static void resetForTests() {
        synchronized (LOCK) {
            marked = null;
            PASSED.clear();
            BEGUN.clear();
        }
    }
}
