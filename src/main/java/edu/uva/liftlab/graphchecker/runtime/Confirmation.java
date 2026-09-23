package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The edges a CONFIRM run is expected to take, and whether it took them.
 *
 * <p>THE RULE.  SAT says the model satisfies the formula; CONFIRM says the
 * program agrees: the model's roots are planted, the selected path's
 * session schedule is held (strict prefix to the anchor, timeouts after --
 * an obligation replay), no flip is forced, and the run is required to (a)
 * not diverge from the schedule before the anchor, (b) take every edge the
 * model chose, (c) observe the fatal at the anchor.  This class is (b):
 * {@code explore.ConfirmMain} writes {@value #FILE} beside the focus row --
 * one {@code WIRE} row per selected arm (consumer endpoint id, producer
 * endpoint id), one {@code STATE} row per state join of the selected path
 * (reader endpoint id, writer endpoint id, version), the {@code MARKER}
 * polarities and the {@code ANCHOR} -- and the existing hooks compare what
 * the run pairs and joins against it.  CHECKING, NOT ENFORCING: the run is
 * scheduled by the session's schedule as every focused replay is, and a
 * difference is filed as a {@code CONFIRM_MISMATCH} gap naming expected and
 * actual.  A replay handed no such file compares nothing.</p>
 *
 * <p>A WIRE edge is compared where the producer is known, at the attach
 * ({@code RowRuntime.attachedAt}).  A STATE edge is compared at the close:
 * a read's observed version names a write of the same run, and the write
 * log of an activation is read out at its end, so the writer of a version
 * may be published after the read that saw it.  Both kinds also mismatch
 * when the consumer, or the reader, never ran at all: an edge the model
 * chose that the run never took is not an edge the run agreed on.</p>
 */
public final class Confirmation {
    /** The file the worker hands the replay, beside the focus row. */
    public static final String FILE = "expected_edges.jsonl";

    private static final Object LOCK = new Object();
    private static boolean loaded;
    /** Consumer endpoint id -> the producer endpoint id the model chose. */
    private static final Map<String, String> WIRE =
            new LinkedHashMap<String, String>();
    /**
     * Writer endpoint id -> version, for every join of a declared cell's
     * PLACEHOLDER: the mint of a declared cell lands on whichever
     * occurrence of the region reads it first (17960's two FSImageSaver
     * threads), so the edge is held by the writer the mint observed and
     * not by the reader's occurrence.
     */
    private static final Map<String, String> MINT =
            new LinkedHashMap<String, String>();
    /** Every (location@version) a placeholder of this run observed. */
    private static final Set<String> MINTED =
            new LinkedHashSet<String>();
    /** Reader endpoint id -> the writer endpoint id the model joined to. */
    private static final Map<String, String> STATE =
            new LinkedHashMap<String, String>();
    /** Reader endpoint id -> the version the model joined to (report). */
    private static final Map<String, String> VERSION =
            new LinkedHashMap<String, String>();
    /** Consumer endpoint id -> the producer this run paired it with. */
    private static final Map<String, String> ATTACHED =
            new LinkedHashMap<String, String>();
    /** Reader endpoint id -> (location key, observed version) this run. */
    private static final Map<String, String> READ =
            new LinkedHashMap<String, String>();
    /** (location key, version) -> the writer endpoint id of this run. */
    private static final Map<String, String> WROTE =
            new LinkedHashMap<String, String>();

    private Confirmation() {
    }

    /** Whether this replay was handed expected edges at all. */
    static boolean expected() {
        load();
        synchronized (LOCK) {
            return !WIRE.isEmpty() || !STATE.isEmpty() || !MINT.isEmpty();
        }
    }

    /**
     * One delivery this run paired: the mismatch to file, or {@code ""}.
     *
     * <p>Compared here and not at the close because the producer is known
     * here; the consumer is remembered so the close can name the expected
     * consumers that never attached.</p>
     */
    static String attached(Endpoint consumer, Endpoint producer) {
        if (!expected() || consumer == null) return "";
        String actual = producer == null ? "" : producer.id();
        synchronized (LOCK) {
            ATTACHED.put(consumer.id(), actual);
            String chosen = WIRE.get(consumer.id());
            if (chosen == null || chosen.equals(actual)) return "";
            return "WIRE " + consumer.id() + ": the model chose producer "
                    + chosen + ", the run paired "
                    + (actual.isEmpty() ? "no export" : actual);
        }
    }

    /** One write this run published, by the key a read's version names. */
    static void wrote(LocationId location, long version, Endpoint writer) {
        if (!expected() || location == null || writer == null) return;
        synchronized (LOCK) {
            WROTE.put(key(location, version), writer.id());
        }
    }

    /**
     * One read this run published, with the version it observed; a
     * placeholder states its mint's version too ({@link
     * ReadRow#mintVersion}) and is remembered by the cell it observed.
     */
    static void read(Endpoint reader, LocationId location,
                     long observedVersion, long mintVersion) {
        if (!expected() || reader == null || location == null) return;
        synchronized (LOCK) {
            if (mintVersion != ReadRow.UNKNOWN_VERSION) {
                MINTED.add(key(location, observedVersion));
            }
            if (!STATE.containsKey(reader.id())) return;
            READ.put(reader.id(), key(location, observedVersion));
        }
    }

    /**
     * Every STATE and WIRE edge the run did not take, at the close.
     *
     * <p>A reader (or consumer) the run never published is a mismatch
     * too: the model's edge starts at an event that did not happen.</p>
     */
    static List<String> close() {
        List<String> mismatches = new ArrayList<String>();
        if (!expected()) return mismatches;
        synchronized (LOCK) {
            for (Map.Entry<String, String> edge : WIRE.entrySet()) {
                if (ATTACHED.containsKey(edge.getKey())) continue;
                mismatches.add("WIRE " + edge.getKey() + ": the model chose"
                        + " producer " + edge.getValue()
                        + ", the run never attached at this consumer");
            }
            for (Map.Entry<String, String> edge : MINT.entrySet()) {
                boolean taken = false;
                List<String> observed = new ArrayList<String>();
                for (String minted : MINTED) {
                    String writer = WROTE.get(minted);
                    observed.add(minted + (writer == null ? "" : " by "
                            + writer));
                    taken |= edge.getKey().equals(writer);
                }
                if (taken) continue;
                mismatches.add("STATE mint: the model joined a declared "
                        + "cell's placeholder to writer " + edge.getKey()
                        + " (version " + edge.getValue() + "), and no "
                        + "placeholder of the run observed a version that "
                        + "writer wrote" + (observed.isEmpty() ? ""
                        : "; the run's placeholders observed "
                        + observed));
            }
            for (Map.Entry<String, String> edge : STATE.entrySet()) {
                String observed = READ.get(edge.getKey());
                String version = VERSION.get(edge.getKey());
                if (observed == null) {
                    mismatches.add("STATE " + edge.getKey() + ": the model"
                            + " joined this read to writer "
                            + edge.getValue() + " (version " + version
                            + "), the run never read here");
                    continue;
                }
                String writer = WROTE.get(observed);
                if (edge.getValue().equals(writer)) continue;
                mismatches.add("STATE " + edge.getKey() + ": the model"
                        + " joined this read to writer " + edge.getValue()
                        + " (version " + version + "), the run observed "
                        + observed + (writer == null
                        ? ", a version no write of this run states"
                        : " written by " + writer));
            }
        }
        return mismatches;
    }

    /** The one spelling a read's observed version and a write share. */
    private static String key(LocationId location, long version) {
        return location.kind() + "/" + location.owner() + "#"
                + location.slot() + "@" + version;
    }

    private static void load() {
        synchronized (LOCK) {
            if (loaded) return;
            loaded = true;
            Path file = FocusedReplay.workerFile(FILE);
            if (file == null) return;
            try {
                for (JsonObject row : RowCodec.readJsonl(file)) {
                    String kind = text(row, "kind");
                    if ("WIRE".equals(kind)) {
                        WIRE.put(text(row, "consumer"), text(row, "producer"));
                    } else if ("STATE".equals(kind)
                            && row.has("mint") && !row.get("mint").isJsonNull()
                            && row.get("mint").getAsBoolean()) {
                        MINT.put(text(row, "writer"), text(row, "version"));
                    } else if ("STATE".equals(kind)) {
                        STATE.put(text(row, "reader"), text(row, "writer"));
                        VERSION.put(text(row, "reader"), text(row, "version"));
                    }
                    // MARKER rows are the root assignments the focus row
                    // already plants; ANCHOR is what the driver reads off
                    // the target row.  Neither is compared here.
                }
            } catch (IOException | RuntimeException unreadable) {
                // Stated by the file's absence of effect: nothing loaded
                // compares nothing, and the driver reads the mismatch
                // gaps, of which there are then none.  The reader of the
                // confirmation sees the replay log line.
                System.err.println("Causynth could not read " + file + ": "
                        + unreadable);
                WIRE.clear();
                STATE.clear();
                VERSION.clear();
                MINT.clear();
            }
        }
    }

    private static String text(JsonObject row, String member) {
        return row.has(member) && !row.get(member).isJsonNull()
                ? row.get(member).getAsString() : "";
    }

    public static void resetForTests() {
        synchronized (LOCK) {
            loaded = false;
            WIRE.clear();
            STATE.clear();
            VERSION.clear();
            MINT.clear();
            MINTED.clear();
            ATTACHED.clear();
            READ.clear();
            WROTE.clear();
        }
    }
}
