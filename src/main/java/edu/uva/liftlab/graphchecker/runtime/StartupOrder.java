package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

public final class StartupOrder {
    private static final Object LOCK = new Object();
    private static Map<String, List<String>> marked;
    private static final Map<String, Set<String>> PASSED =
            new HashMap<String, Set<String>>();
    private static final Map<String, Integer> BEGUN =
            new HashMap<String, Integer>();

    private StartupOrder() {
    }

    static String[] begin(String step, String who) {
        String named = trimmed(step);
        String by = trimmed(who);
        if (named.isEmpty() || by.isEmpty()) return null;
        synchronized (LOCK) {
            int n = BEGUN.merge(named + "\n" + by, 1, Integer::sum) - 1;
            String pass = by + "#" + n;
            List<String> order = markedLocked().get(named);
            int at = order == null ? -1 : order.indexOf(pass);
            Set<String> passed = passedLocked(named);
            List<String> before = at <= 0 ? new ArrayList<String>()
                    : new ArrayList<String>(order.subList(0, at));
            if (RecordingWindow.opened() && !passed.containsAll(before)) {
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

    static void done(String[] pass) {
        if (pass == null) return;
        synchronized (LOCK) {
            passedLocked(pass[0]).add(pass[1]);
            LOCK.notifyAll();
        }
        String who = pass[1].substring(0, pass[1].lastIndexOf('#'));
        ScheduleLog.writeMark(RowCodec.writeScheduleStartup(pass[0], who));
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
            }
        }
        return marked;
    }
}
