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

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * A native reproduction's plant (ADHOC-INFRA WP5.D): the fault markers a
 * confirmed witness moved, planted in the recording weave on a stock JDK, so
 * a finding is run again without the concolic VM ({@code run_engine.sh}
 * REPRODUCE).
 *
 * <p>{@code -Dcausynth.plant=<file>} names the plant, one JSONL row per
 * marker: {@code {"kind":"MARKER","occurrence":<occurrence id>,"siteId":
 * <site>,"value":true|false}}, CONFIRM's world written by CONFIRM's own code
 * ({@code explore.ConfirmMain --plant}).  A marker call answers a row's
 * value when its call site is the row's site and a region occurrence
 * enclosing it on this thread has the row's id -- by {@link
 * OccurrenceAddress#id}, as a focused replay matches its occurrences --
 * inside the recording window; otherwise, and always without a plant, its
 * recorded polarity {@code false}.  Every planted answer is a {@link
 * #APPLIED} trace row.</p>
 */
public final class RecordingPlant {
    static final String PROPERTY = "causynth.plant";
    /** The trace event of one planted answer. */
    static final String APPLIED = "PLANT_APPLIED";
    /** The one kind phase 1 plants: a {@code Debug.makeSymbolicBoolean}. */
    public static final String MARKER = "MARKER";
    public static final String KIND = "kind";
    public static final String OCCURRENCE = "occurrence";
    public static final String SITE = "siteId";
    public static final String VALUE = "value";

    /** Site, then occurrence id, then the planted value. */
    private static volatile Map<String, Map<String, Boolean>> planted;

    private RecordingPlant() {
    }

    /** Whether this run plants a world: a native reproduction, where the
     *  workload's checks of the recording's world do not hold
     *  ({@link CausynthTraceRecorder#replaying}). */
    static boolean planting() {
        return !System.getProperty(PROPERTY, "").trim().isEmpty();
    }

    /** The marker {@code name}'s answer at the call running now. */
    static boolean marker(String name) {
        Map<String, Map<String, Boolean>> rows = planted();
        if (rows.isEmpty() || !RecordingWindow.opened()) return false;
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

    private static Map<String, Map<String, Boolean>> planted() {
        Map<String, Map<String, Boolean>> rows = planted;
        if (rows != null) return rows;
        synchronized (RecordingPlant.class) {
            if (planted == null) {
                String file = System.getProperty(PROPERTY, "").trim();
                try {
                    planted = file.isEmpty()
                            ? Collections.<String, Map<String, Boolean>>emptyMap()
                            : read(Paths.get(file));
                } catch (IOException | RuntimeException unreadable) {
                    // A run told to plant that cannot is no reproduction.
                    throw new IllegalStateException("the plant -D" + PROPERTY
                            + "=" + file + " is unreadable: "
                            + unreadable.getMessage(), unreadable);
                }
            }
            return planted;
        }
    }

    /** A plant file's rows, by site and occurrence id; any other kind, or a
     *  row naming no site, occurrence or boolean value, is refused. */
    static Map<String, Map<String, Boolean>> read(Path file)
            throws IOException {
        Map<String, Map<String, Boolean>> rows =
                new LinkedHashMap<String, Map<String, Boolean>>();
        for (JsonObject row : ArtifactIO.readJsonl(file)) {
            String site = optionalString(row, SITE);
            String occurrence = optionalString(row, OCCURRENCE);
            if (!MARKER.equals(optionalString(row, KIND)) || site.isEmpty()
                    || occurrence.isEmpty() || !row.has(VALUE)
                    || !row.get(VALUE).isJsonPrimitive()
                    || !row.getAsJsonPrimitive(VALUE).isBoolean()) {
                throw new IOException("not a marker plant row: " + row);
            }
            rows.computeIfAbsent(site,
                    key -> new LinkedHashMap<String, Boolean>())
                    .put(occurrence, row.get(VALUE).getAsBoolean());
        }
        return Collections.unmodifiableMap(rows);
    }
}
