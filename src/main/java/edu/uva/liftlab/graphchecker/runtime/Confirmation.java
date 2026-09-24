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
 * program agrees: the model's world is planted, the reads the model rests on
 * are held to the versions it chose ({@link Versions}), no flip is forced,
 * and the run is required to (a) take every edge the model chose and (b)
 * observe the fatal at the anchor.  This class is (a):
 * {@code explore.ConfirmMain} writes {@value #FILE} beside the focus row --
 * one {@code WIRE} row per selected arm (consumer endpoint id, producer
 * endpoint id), one {@code STATE} row per placeholder the model joined to a
 * writer, the {@code MARKER} polarities and the {@code ANCHOR} -- and the
 * existing hooks compare what the run pairs and joins against it.  The state
 * joins the model chose are the focus row's versions: {@link Versions}
 * holds them and refuses the verdict where one was not realized, and a held
 * read the run never made is an edge not taken, stated here.  A difference
 * is filed as a {@code CONFIRM_MISMATCH} gap naming expected and actual; a
 * replay handed no expected edges and no versions compares nothing.</p>
 *
 * <p>A WIRE edge is compared where the producer is known, at the attach
 * ({@code RowRuntime.attachedAt}).  A placeholder's edge is compared at the
 * close: a read's observed version names a write of the same run, and the
 * write log of an activation is read out at its end, so the writer of a
 * version may be published after the read that saw it.  Both kinds also
 * mismatch when the consumer, or the reader, never ran at all: an edge the
 * model chose that the run never took is not an edge the run agreed on.</p>
 */
public final class Confirmation {
    /** The file the worker hands the replay, beside the focus row. */
    public static final String FILE = "expected_edges.jsonl";

    private static final Object LOCK = new Object();
    private static boolean loaded;
    /** Whether this replay is a confirmation: it was handed {@value #FILE}. */
    private static boolean confirming;
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
    /** Consumer endpoint id -> the producer this run paired it with. */
    private static final Map<String, String> ATTACHED =
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
            return !WIRE.isEmpty() || !MINT.isEmpty();
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
     * One read this run published: a placeholder states its mint's version
     * ({@link ReadRow#mintVersion}) and is remembered by the cell it
     * observed.
     */
    static void read(Endpoint reader, LocationId location,
                     long observedVersion, long mintVersion) {
        if (!expected() || reader == null || location == null
                || mintVersion == ReadRow.UNKNOWN_VERSION) {
            return;
        }
        synchronized (LOCK) {
            MINTED.add(key(location, observedVersion));
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
        load();
        if (!confirming) return mismatches;
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
        }
        // A held read the run never made is a state join the model chose
        // that the run did not take; one it made and saw another writer's
        // version is refused by the verdict (Versions#unrealized).
        Set<String> observed = Versions.readersObserved();
        for (Map.Entry<String, String> held : Versions.held().entrySet()) {
            if (observed.contains(held.getKey())) continue;
            mismatches.add("STATE " + held.getKey() + ": the model joined"
                    + " this read to writer " + held.getValue()
                    + ", the run never read here");
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
            confirming = true;
            try {
                for (JsonObject row : RowCodec.readJsonl(file)) {
                    String kind = text(row, "kind");
                    if ("WIRE".equals(kind)) {
                        WIRE.put(text(row, "consumer"), text(row, "producer"));
                    } else if ("STATE".equals(kind)) {
                        MINT.put(text(row, "writer"), text(row, "version"));
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
            confirming = false;
            WIRE.clear();
            MINT.clear();
            MINTED.clear();
            ATTACHED.clear();
            WROTE.clear();
        }
    }
}
