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
 * <p>CONFIRM plants the model's roots, holds the path's schedule, forces no
 * flip, and requires (a) every model edge taken and (b) the fatal at the
 * anchor.  This class is (a), from {@value #FILE} written by
 * {@code explore.ConfirmMain}.  CHECKING, NOT ENFORCING: a difference is a
 * {@code CONFIRM_MISMATCH} gap.</p>
 *
 * <p>WIRE is compared at the attach, where the producer is known; STATE at
 * the close, since a writer's log is read out after the read that saw it.
 * An expected consumer or reader that never ran is a mismatch too.</p>
 */
public final class Confirmation {
    public static final String FILE = "expected_edges.jsonl";

    private static final Object LOCK = new Object();
    private static boolean loaded;
    /** Consumer endpoint id -> the producer endpoint id the model chose. */
    private static final Map<String, String> WIRE =
            new LinkedHashMap<String, String>();
    /**
     * Writer endpoint id -> version for a declared cell's PLACEHOLDER join;
     * keyed by writer because the mint lands on whichever occurrence reads
     * first.
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

    static boolean expected() {
        load();
        synchronized (LOCK) {
            return !WIRE.isEmpty() || !STATE.isEmpty() || !MINT.isEmpty();
        }
    }

    /** One delivery this run paired: the mismatch to file, or {@code ""}. */
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

    static void wrote(LocationId location, long version, Endpoint writer) {
        if (!expected() || location == null || writer == null) return;
        synchronized (LOCK) {
            WROTE.put(key(location, version), writer.id());
        }
    }

    /** One read; a placeholder ({@link ReadRow#mintVersion}) is also kept. */
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

    /** Every STATE and WIRE edge the run did not take, at the close. */
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
                    // MARKER and ANCHOR are checked elsewhere.
                }
            } catch (IOException | RuntimeException unreadable) {
                // Trap: an unreadable file compares nothing and files no
                // gap; only this log line says so.
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
