package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicBoolean;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * A native reproduction's plant (ADHOC-INFRA WP5.D): the fault markers a
 * confirmed witness moved, planted in the recording weave on a stock JDK, so
 * a finding is run again without the concolic VM ({@code run_engine.sh}
 * REPRODUCE), and the one question such a run answers: does the planted
 * world take the throw's fatal arm at the claim's anchor.
 *
 * <p>{@code -Dcausynth.plant=<file>} names the plant, JSONL written by
 * CONFIRM's own code ({@code explore.ConfirmMain --plant}):</p>
 * <ul>
 *   <li>{@code {"kind":"MARKER","occurrence":<occurrence id>,"siteId":
 *   <call site>,"value":true|false}} per marker of CONFIRM's world.  A
 *   marker call answers a row's value when its call site is the row's site
 *   and a region occurrence enclosing it on this thread has the row's id --
 *   by {@link OccurrenceAddress#id}, as a focused replay matches its
 *   occurrences -- inside the recording window; otherwise, and always
 *   without a plant, its recorded polarity {@code false}.  Every planted
 *   answer is an {@link #APPLIED} trace row.</li>
 *   <li>{@code {"kind":"TARGET","occurrence":<the anchor's id>,"siteId":
 *   <a TARGET_SITE guard>,"value":<its fatal arm>}} per guard of the
 *   target.  A decision there that takes the fatal arm inside the window is
 *   a {@link #FATAL} trace row, saying whether an enclosing occurrence is
 *   the anchor; at the anchor the run ends ({@link JUnitMethodRunner#exit}),
 *   its question answered, as a focused replay ends at its witness.</li>
 * </ul>
 */
public final class RecordingPlant {
    static final String PROPERTY = "causynth.plant";
    /** The trace event of one planted answer. */
    static final String APPLIED = "PLANT_APPLIED";
    /** The trace event of one decision of the planted world's fatal arm. */
    static final String FATAL = "PLANT_FATAL";
    /** A {@code Debug.makeSymbolicBoolean} the plant answers. */
    public static final String MARKER = "MARKER";
    /** A guard of the target and its fatal arm. */
    public static final String TARGET = "TARGET";
    public static final String KIND = "kind";
    public static final String OCCURRENCE = "occurrence";
    public static final String SITE = "siteId";
    public static final String VALUE = "value";

    /** Read once: the JVM's own property. */
    private static final boolean PLANTING =
            !System.getProperty(PROPERTY, "").trim().isEmpty();
    private static volatile Plant plant;
    private static final AtomicBoolean ENDED = new AtomicBoolean();

    private RecordingPlant() {
    }

    /** Whether this run plants a world: a native reproduction, where the
     *  workload's checks of the recording's world do not hold
     *  ({@link CausynthTraceRecorder#replaying}). */
    static boolean planting() {
        return PLANTING;
    }

    /** One plant file: its markers and its target. */
    static final class Plant {
        /** Site, then occurrence id, then the planted value. */
        final Map<String, Map<String, Boolean>> markers;
        /** Guard site -> its fatal arm. */
        final Map<String, Boolean> fatalArms;
        /** The claim's anchor, by occurrence id. */
        final String anchor;

        Plant(Map<String, Map<String, Boolean>> markers,
              Map<String, Boolean> fatalArms, String anchor) {
            this.markers = markers;
            this.fatalArms = fatalArms;
            this.anchor = anchor;
        }
    }

    /** The marker {@code name}'s answer at the call running now. */
    static boolean marker(String name) {
        if (!PLANTING || !RecordingWindow.opened()) return false;
        Map<String, Map<String, Boolean>> rows = plant().markers;
        CausynthTraceRecorder.ActiveCallSiteContext site =
                CausynthTraceRecorder.currentCallSiteContext();
        if (site == null) return false;
        String occurrence = plantedOccurrence(rows, site.siteId(),
                CausynthTraceRecorder.enclosingOccurrences());
        if (occurrence == null) return false;
        boolean value = rows.get(site.siteId()).get(
                OccurrenceAddress.parse(occurrence).id());
        CausynthTraceRecorder.plantApplied(name, site.siteId(), occurrence,
                value);
        return value;
    }

    /** A decision the recording observed ({@code outcome} null when it took
     *  no arm a guard names): at a target guard's fatal arm, stated, and at
     *  the anchor the run's end. */
    static void decided(String siteId, Boolean outcome) {
        if (!PLANTING || outcome == null) return;
        Plant rows = plant();
        if (!outcome.equals(rows.fatalArms.get(siteId))
                || !RecordingWindow.opened()) {
            return;
        }
        List<String> enclosing = CausynthTraceRecorder.enclosingOccurrences();
        String anchor = anchorOf(enclosing, rows.anchor);
        CausynthTraceRecorder.plantFatal(siteId, anchor != null ? anchor
                : enclosing.isEmpty() ? "" : enclosing.get(0), anchor != null);
        if (anchor != null && ENDED.compareAndSet(false, true)) {
            end(siteId, anchor);
        }
    }

    /** Of the occurrences enclosing a decision, the anchor's, or null. */
    static String anchorOf(List<String> enclosing, String anchor) {
        for (String occurrence : enclosing) {
            if (OccurrenceAddress.parse(occurrence).id().equals(anchor)) {
                return occurrence;
            }
        }
        return null;
    }

    /** Of the occurrences enclosing a call at {@code site}, innermost first,
     *  the first a row plants there, or null. */
    static String plantedOccurrence(Map<String, Map<String, Boolean>> rows,
                                    String site, List<String> enclosing) {
        Map<String, Boolean> byOccurrence = rows.get(site);
        if (byOccurrence == null) return null;
        for (String occurrence : enclosing) {
            if (byOccurrence.containsKey(
                    OccurrenceAddress.parse(occurrence).id())) {
                return occurrence;
            }
        }
        return null;
    }

    /** The run's one end, on a thread of its own: the decision's thread is
     *  the workload's, and the end waits for what is live to settle. */
    private static void end(final String siteId, final String anchor) {
        ThreadGroup root = Thread.currentThread().getThreadGroup();
        while (root.getParent() != null) root = root.getParent();
        new Thread(root, new Runnable() {
            @Override
            public void run() {
                System.err.println("Causynth " + java.time.Instant.now()
                        + ": the native run ends AT_ANCHOR: the planted world"
                        + " took the fatal arm of " + siteId + " at "
                        + anchor);
                JUnitMethodRunner.exit(0);
            }
        }, "causynth-plant-end").start();
    }

    private static Plant plant() {
        Plant rows = plant;
        if (rows != null) return rows;
        synchronized (RecordingPlant.class) {
            if (plant == null) {
                String file = System.getProperty(PROPERTY, "").trim();
                try {
                    plant = read(Paths.get(file));
                } catch (IOException | RuntimeException unreadable) {
                    // A run told to plant that cannot is no reproduction.
                    throw new IllegalStateException("the plant -D" + PROPERTY
                            + "=" + file + " is unreadable: "
                            + unreadable.getMessage(), unreadable);
                }
            }
            return plant;
        }
    }

    /** A plant file's rows.  A row of another kind, or naming no site,
     *  occurrence or boolean value, is refused; so is a plant whose target
     *  rows name no anchor or two, since the run would answer nothing. */
    static Plant read(Path file) throws IOException {
        Map<String, Map<String, Boolean>> markers =
                new LinkedHashMap<String, Map<String, Boolean>>();
        Map<String, Boolean> fatalArms = new LinkedHashMap<String, Boolean>();
        String anchor = null;
        for (JsonObject row : ArtifactIO.readJsonl(file)) {
            String kind = optionalString(row, KIND);
            String site = optionalString(row, SITE);
            String occurrence = optionalString(row, OCCURRENCE);
            if (!(MARKER.equals(kind) || TARGET.equals(kind))
                    || site.isEmpty() || occurrence.isEmpty()
                    || !row.has(VALUE) || !row.get(VALUE).isJsonPrimitive()
                    || !row.getAsJsonPrimitive(VALUE).isBoolean()) {
                throw new IOException("not a plant row: " + row);
            }
            boolean value = row.get(VALUE).getAsBoolean();
            if (MARKER.equals(kind)) {
                markers.computeIfAbsent(site,
                        key -> new LinkedHashMap<String, Boolean>())
                        .put(occurrence, value);
            } else if (anchor == null || anchor.equals(occurrence)) {
                anchor = occurrence;
                fatalArms.put(site, value);
            } else {
                throw new IOException("the plant's target rows name two "
                        + "anchors, " + anchor + " and " + occurrence);
            }
        }
        if (anchor == null) {
            throw new IOException("the plant names no target: " + file);
        }
        return new Plant(Collections.unmodifiableMap(markers),
                Collections.unmodifiableMap(fatalArms), anchor);
    }
}
