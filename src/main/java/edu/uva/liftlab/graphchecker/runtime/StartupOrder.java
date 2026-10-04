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
 * THE order takers pass a startup step an adapter names: a step that builds
 * state a replay reads, taken before the window, where no slot of the
 * schedule holds it (IDENTITY §8).  HDFS's is the NameNode adding a
 * DataNode ({@code FSNamesystem#registerDatanode}): its NetworkTopology
 * orders DataNodes as they are added, and block placement picks a pipeline
 * by position in it, so a replay whose DataNodes were added in another
 * order wrote its blocks to other nodes though it drew what its recording
 * drew (hdfs-adhoc-01/43, STATUS open defect 40).
 *
 * <p>The recording states each completion as a {@code STARTUP} mark of its
 * schedule (step, who, and whether its window had not opened yet: {@code
 * pre}), in completion order, handed on with every order ({@code
 * explore.SchedulePrefix}).  A replay holds a taker whose pass is marked
 * {@code pre} until every pass marked before its own completed it, whatever
 * its own window's state -- the two passes' windows may open at different
 * points of the start-up (hdfs-adhoc-43, round SS5: two DataNodes added in
 * the other order, no hold) -- a taker's n-th pass standing for its n-th
 * mark; inside its own window the held thread is away from the schedule's
 * frontier ({@code ScheduleLog#elsewhere}).  At most one schedule timeout,
 * after which the missing ones are given up by name ({@code
 * SCHEDULE_DIVERGED}); an interrupt ends the hold by name too.  A pass
 * marked inside the recording's window is held by the schedule's slots;
 * one this replay takes before its own window opens is named ({@code
 * startup-unheld}).  HDFS's taker is the NameNode adding a DataNode, named
 * by the DataNode's UUID, the same in both passes: its draw is keyed
 * ({@code Randoms}).</p>
 */
public final class StartupOrder {
    private static final Object LOCK = new Object();
    /** Per step, the passes the order handed to this replay marks, in their
     *  order ({@code who#n}); read once. */
    private static Map<String, List<String>> marked;
    /** Per step, the passes completed in this run, or given up. */
    private static final Map<String, Set<String>> PASSED =
            new HashMap<String, Set<String>>();
    /** The marked passes the recording took before its window opened
     *  ({@code step\nwho#n}): held whatever this replay's window. */
    private static final Set<String> PRE = new HashSet<String>();
    /** Per step and taker, how often it began the step in this run. */
    private static final Map<String, Integer> BEGUN =
            new HashMap<String, Integer>();

    private StartupOrder() {
    }

    /**
     * {@code who} is about to take {@code step}: in a replay, a pass its
     * recording marked {@code pre} is held until the passes marked before
     * its own completed, whatever this replay's window.
     *
     * @return what {@link #done} takes, or null when nothing is named
     */
    static String[] begin(String step, String who) {
        String named = Text.safe(step);
        String by = Text.safe(who);
        if (named.isEmpty() || by.isEmpty()) return null;
        synchronized (LOCK) {
            int n = BEGUN.merge(named + "\n" + by, 1, Integer::sum) - 1;
            String pass = by + "#" + n;
            List<String> order = markedLocked().get(named);
            int at = order == null ? -1 : order.indexOf(pass);
            Set<String> passed = passedLocked(named);
            List<String> before = at <= 0 ? new ArrayList<String>()
                    : new ArrayList<String>(order.subList(0, at));
            if (at >= 0 && !PRE.contains(named + "\n" + pass)) {
                // Marked inside the recording's window: its slots order it,
                // unless this replay takes it before its own window opens.
                if (!RecordingWindow.opened()) {
                    ScheduleLog.diverged("startup-unheld#" + named, pass
                            + " takes " + named + " before this replay's"
                            + " window opened, where its recording took it"
                            + " inside its window: nothing orders it");
                }
                before.clear();
            } else if (RecordingWindow.opened() && !passed.containsAll(before)) {
                // Held inside this replay's window: the schedule sees it.
                ScheduleLog.elsewhere();
            }
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
                    before.removeAll(passed);
                    ScheduleLog.diverged("startup#" + named, pass + " took "
                            + named + " when interrupted while waiting for "
                            + before + ", marked before it");
                    break;
                }
            }
            return new String[] {named, pass};
        }
    }

    /** The pass {@link #begin} returned completed: marked, and the takers
     *  held behind it go on. */
    static void done(String[] pass) {
        if (pass == null) return;
        synchronized (LOCK) {
            passedLocked(pass[0]).add(pass[1]);
            LOCK.notifyAll();
        }
        String who = pass[1].substring(0, pass[1].lastIndexOf('#'));
        ScheduleLog.writeMark(RowCodec.writeScheduleStartup(pass[0], who,
                !RecordingWindow.opened()));
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
                String who = mark.get("who").getAsString();
                int n = passes.merge(step + "\n" + who, 1, Integer::sum) - 1;
                marked.computeIfAbsent(step, ignored -> new ArrayList<String>())
                        .add(who + "#" + n);
                if (mark.get("pre").getAsBoolean()) {
                    PRE.add(step + "\n" + who + "#" + n);
                }
            }
        }
        return marked;
    }

    /** Test seam: a fresh run. */
    static void resetForTests() {
        synchronized (LOCK) {
            marked = null;
            PRE.clear();
            PASSED.clear();
            BEGUN.clear();
        }
    }
}
