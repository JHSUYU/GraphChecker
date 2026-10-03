package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * The edges a CONFIRM run is expected to take, the order it is held to, and
 * whether it took them.
 *
 * <p>CONFIRM plants the model's roots, forces no flip, and requires (a) every
 * model edge taken and (b) the fatal at the anchor.  This class is (a), from
 * {@value #FILE} written by {@code explore.ConfirmMain}.  The recorded order is
 * not held (only a WAKE waits for what it followed); the MODEL's is: an
 * {@code ORDER} row holds one method activation's entry until the activations
 * it names have exited -- a join's writer before its reader, every other
 * writer of the location outside the two -- at the frame and region hooks
 * every pass weaves ({@code Identity}); the held activation is the last one
 * entered before the ordered event ({@code ConfirmMain}).  Endpoints and
 * activations are compared as every delivery of their stored message names
 * them ({@link #id}), and a STATE reader at any turn of the loops on its
 * path ({@link #anyTurn}).  An activation that waits out
 * {@link #ORDER_TIMEOUT_PROPERTY} proves the model's order unrealizable in
 * this program: it goes on, and the stall is a {@code CONFIRM_MISMATCH}, so
 * the claim is not confirmed.  Any other difference is one too.</p>
 *
 * <p>An obligation replay whose world plants pairings
 * ({@code explore.ObligationFactory}) is handed the same rows over them:
 * held to the same order, and an edge it did not take un-admits it
 * ({@code FocusedReplay}, {@code PAIRING_UNTAKEN}).</p>
 *
 * <p>WIRE is compared at the attach, where the producer is known -- a
 * codec's hole at its mint, by the store version its message was and the
 * text it decoded too (WIRE-CODEC §6.5); STATE at the close, since a
 * writer's log is read out after the read that saw it.
 * An expected consumer or reader that never ran is a mismatch too, and so is
 * a CONFIRM run whose edges could not be read: it compared nothing, and the
 * fatal alone confirms no model.</p>
 */
public final class Confirmation {
    public static final String FILE = "expected_edges.jsonl";
    /**
     * The writer a STATE row names for a location's INITIAL
     * ({@code contract.WriteRow#initial}): no occurrence wrote it, and the
     * access its row stands at is whichever first observed the location.
     */
    public static final String INITIAL = "INITIAL";
    /** How long an activation waits for those ordered before it, in ms. */
    public static final String ORDER_TIMEOUT_PROPERTY =
            "causynth.confirm.order.timeout.ms";
    static final long ORDER_TIMEOUT_MS = 300000L;

    private static final Object LOCK = new Object();
    private static boolean loaded;
    /** Consumer endpoint id -> the delivery the model chose there. */
    private static final Map<String, Wire> WIRE =
            new LinkedHashMap<String, Wire>();
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
    /** STATE reader endpoint id -> its id at any turn ({@link #anyTurn}). */
    private static final Map<String, String> TURNS =
            new LinkedHashMap<String, String>();
    /** The any-turn ids {@link #TURNS} names. */
    private static final Set<String> TURNED = new HashSet<String>();
    /** Any-turn reader id -> every (location key, version) this run's
     *  reads there observed. */
    private static final Map<String, Set<String>> READ_TURNS =
            new LinkedHashMap<String, Set<String>>();
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
    /** Activation -> the activations the model orders before it. */
    private static final Map<String, Set<String>> BEFORE =
            new HashMap<String, Set<String>>();
    /** The activations that have exited. */
    private static final Set<String> EXITED = new HashSet<String>();
    /** The order stalls: what the model ordered and this run could not. */
    private static final List<String> UNREALIZED = new ArrayList<String>();
    /** Why this CONFIRM run's edges could not be read, or "". */
    private static String unread = "";
    /** 0 not read yet, 1 no order, 2 an order is held; read per frame. */
    private static volatile int ordering;

    private Confirmation() {
    }

    /**
     * One delivery the model chose: its producer endpoint; for a codec's
     * hole, the store version its message was (null for an exchange, whose
     * correlation is its run's own) and the text the hole must decode to
     * (null where the model's value rests on a clock, which a replay reads
     * afresh).
     */
    private static final class Wire {
        private final String producer;
        private final String messageKey;
        private final String value;

        private Wire(String producer, String messageKey, String value) {
            this.producer = producer;
            this.messageKey = messageKey;
            this.value = value;
        }
    }

    static boolean expected() {
        load();
        synchronized (LOCK) {
            return !WIRE.isEmpty() || !STATE.isEmpty() || !MINT.isEmpty()
                    || !BEFORE.isEmpty();
        }
    }

    /**
     * One delivery this run paired: the mismatch to file, or {@code ""}.
     * A codec's hole states the message it was decoded from and the text
     * it decoded (null for a declared port's attach).
     */
    static String attached(Endpoint consumer, Endpoint producer,
                           String messageKey, String text) {
        if (!expected() || consumer == null) return "";
        String actual = producer == null ? "" : id(producer);
        synchronized (LOCK) {
            ATTACHED.put(id(consumer), actual);
            Wire chosen = WIRE.get(id(consumer));
            if (chosen == null) return "";
            List<String> differs = new ArrayList<String>();
            if (!chosen.producer.equals(actual)) {
                differs.add("the model chose producer " + chosen.producer
                        + ", the run paired "
                        + (actual.isEmpty() ? "no export" : actual));
            }
            if (chosen.messageKey != null
                    && !chosen.messageKey.equals(messageKey)) {
                differs.add("the model's arm came from message "
                        + chosen.messageKey + ", the run decoded "
                        + messageKey);
            }
            if (chosen.value != null && !chosen.value.equals(text)) {
                differs.add("the model's value is \"" + chosen.value
                        + "\", the run decoded "
                        + (text == null ? "none" : "\"" + text + "\""));
            }
            return differs.isEmpty() ? ""
                    : "WIRE " + id(consumer) + ": " + String.join("; ",
                    differs);
        }
    }

    static void wrote(LocationId location, long version, Endpoint writer,
                      boolean initial) {
        if (!expected() || location == null || writer == null) return;
        synchronized (LOCK) {
            WROTE.put(key(location, version), initial ? INITIAL
                    : id(writer));
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
            if (!TURNED.isEmpty()) {
                String turns = anyTurn(reader);
                if (TURNED.contains(turns)) {
                    READ_TURNS.computeIfAbsent(turns,
                            key -> new LinkedHashSet<String>())
                            .add(key(location, observedVersion));
                }
            }
            if (!STATE.containsKey(id(reader))) return;
            READ.put(id(reader), key(location, observedVersion));
        }
    }

    /**
     * The id CONFIRM knows an endpoint by: the same for every delivery of
     * its occurrence's stored message ({@link Endpoint#anyDelivery}), as
     * {@code explore.ConfirmMain} writes the model's.
     */
    public static String id(Endpoint endpoint) {
        return endpoint.anyDelivery().id();
    }

    /** The id of {@code endpoint} at any turn of its loops ({@link
     *  Endpoint#anyTurn}), named as {@link #id} names it. */
    public static String anyTurn(Endpoint endpoint) {
        return endpoint.anyDelivery().anyTurn().id();
    }

    /** The key CONFIRM knows one method activation by ({@link #id}). */
    public static String activation(OccurrenceAddress occurrence,
                                    ExecutionIndex frames) {
        return Endpoint.activation(occurrence.anyDelivery(), frames);
    }

    /** How many sends {@link #submitter} follows up a chain of claimed
     *  work, as {@code Attribution} follows starters. */
    private static final int SUBMITTER_HOPS = 32;

    /**
     * Where an ORDER holds an event of {@code occurrence} so that it comes
     * after what the model orders before it ({@code explore.ConfirmMain}):
     * null where it runs, unless it runs as claimed work on a consumer
     * thread ({@link ActivationRow#claimed}) -- a server's pipeline applying
     * one request after another.  Held there it would hold every item
     * queued behind it, the writer's among them, so it is held where it was
     * sent: its anchor's producer ({@link ActivationRow#anchorProducer}, the
     * send that started the request), followed up the chain while that
     * send is itself claimed work.  Not its claim's START, which runs on
     * the upstream stage, a consumer too.
     *
     * @throws IllegalStateException naming the chain where no send of it
     *         runs outside claimed work: no hold realizes the order
     */
    public static Endpoint submitter(OccurrenceAddress occurrence,
                                     Function<String, ActivationRow> rows) {
        ActivationRow row = rows.apply(occurrence.id());
        if (row == null || !row.claimed()) return null;
        for (int hop = 0; hop < SUBMITTER_HOPS; hop++) {
            Endpoint send = row.anchorProducer();
            if (send == null) {
                throw new IllegalStateException("ORDER_UNHELD: "
                        + row.occurrence().render() + " runs as claimed "
                        + "work on a consumer thread and names no send of "
                        + "this run that started it, so no hold realizes an "
                        + "order on " + occurrence.render());
            }
            row = rows.apply(send.occurrence().id());
            if (row == null || !row.claimed()) return send;
        }
        throw new IllegalStateException("ORDER_UNHELD: past "
                + SUBMITTER_HOPS + " sends of claimed work above "
                + occurrence.render() + ", no send outside one");
    }

    /** Whether this run is held to an order: every frame hook asks. */
    static boolean ordering() {
        if (ordering == 0) load();
        return ordering == 2;
    }

    /** Holds an activation's entry until those ordered before it exited. */
    static void entering(String activation) {
        synchronized (LOCK) {
            Set<String> before = BEFORE.get(activation);
            if (before == null) return;
            long timeout = Long.getLong(ORDER_TIMEOUT_PROPERTY,
                    ORDER_TIMEOUT_MS);
            long deadline = System.currentTimeMillis() + timeout;
            while (!EXITED.containsAll(before)) {
                long left = deadline - System.currentTimeMillis();
                if (left <= 0L) {
                    Set<String> missing = new LinkedHashSet<String>(before);
                    missing.removeAll(EXITED);
                    UNREALIZED.add("ORDER " + activation + ": the model"
                            + " orders it after " + missing + ", which did not"
                            + " exit within " + timeout + " ms, so this"
                            + " program cannot realize the model's order");
                    return;
                }
                try {
                    LOCK.wait(Math.min(left, 200L));
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                    return;
                }
            }
        }
    }

    static void exited(String activation) {
        synchronized (LOCK) {
            if (EXITED.add(activation)) LOCK.notifyAll();
        }
    }

    /** Every STATE and WIRE edge the run did not take, at the close. */
    static List<String> close() {
        List<String> mismatches = new ArrayList<String>();
        boolean compared = expected();
        synchronized (LOCK) {
            if (!unread.isEmpty()) mismatches.add(unread);
            if (!compared) return mismatches;
            mismatches.addAll(UNREALIZED);
            for (Map.Entry<String, Wire> edge : WIRE.entrySet()) {
                if (ATTACHED.containsKey(edge.getKey())) continue;
                mismatches.add("WIRE " + edge.getKey() + ": the model chose"
                        + " producer " + edge.getValue().producer
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
                if (atAnotherTurn(edge.getKey(), edge.getValue())) continue;
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

    /**
     * Whether a read at this reader's site, at some turn of the loops on its
     * path, observed a version the model's writer wrote: a loop that polls
     * for the write reads it at whichever turn it lands.
     */
    private static boolean atAnotherTurn(String reader, String writer) {
        Set<String> observed = READ_TURNS.get(TURNS.get(reader));
        if (observed == null) return false;
        for (String version : observed) {
            if (writer.equals(WROTE.get(version))) return true;
        }
        return false;
    }

    /** A member a row states, or null when it states none. */
    private static String stated(JsonObject row, String member) {
        return row.has(member) && !row.get(member).isJsonNull()
                ? row.get(member).getAsString() : null;
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
            // Until the rows are read: a hook reached while reading them
            // holds nothing.
            ordering = 1;
            Path file = FocusedReplay.workerFile(FILE);
            if (file == null) {
                // Only a CONFIRM run is handed edges; one that finds none
                // beside its focus row has nothing to compare.
                if (FocusedReplay.confirming()) {
                    unread = "EDGES: this CONFIRM run found no readable "
                            + FILE + " in its worker directory, so no edge"
                            + " the model chose was compared";
                }
                return;
            }
            try {
                for (JsonObject row : RowCodec.readJsonl(file)) {
                    String kind = optionalString(row, "kind");
                    if ("WIRE".equals(kind)) {
                        WIRE.put(optionalString(row, "consumer"), new Wire(
                                optionalString(row, "producer"),
                                stated(row, "messageKey"),
                                stated(row, "value")));
                    } else if ("STATE".equals(kind)
                            && row.has("mint") && !row.get("mint").isJsonNull()
                            && row.get("mint").getAsBoolean()) {
                        MINT.put(optionalString(row, "writer"),
                                optionalString(row, "version"));
                    } else if ("STATE".equals(kind)) {
                        STATE.put(optionalString(row, "reader"),
                                optionalString(row, "writer"));
                        VERSION.put(optionalString(row, "reader"),
                                optionalString(row, "version"));
                        String turns = stated(row, "readerAnyTurn");
                        if (turns != null) {
                            TURNS.put(optionalString(row, "reader"), turns);
                            TURNED.add(turns);
                        }
                    } else if ("ORDER".equals(kind)) {
                        BEFORE.computeIfAbsent(optionalString(row, "after"),
                                key -> new LinkedHashSet<String>())
                                .add(optionalString(row, "before"));
                    }
                    // MARKER and ANCHOR are checked elsewhere.
                }
            } catch (IOException | RuntimeException unreadable) {
                // Half a file is no model: compare nothing, and say so at
                // the close, where it confirms nothing.
                unread = "EDGES: " + file + " could not be read ("
                        + unreadable + "), so no edge the model chose was"
                        + " compared";
                WIRE.clear();
                STATE.clear();
                VERSION.clear();
                TURNS.clear();
                TURNED.clear();
                MINT.clear();
                BEFORE.clear();
            }
            ordering = BEFORE.isEmpty() ? 1 : 2;
        }
    }

    public static void resetForTests() {
        synchronized (LOCK) {
            loaded = false;
            ordering = 0;
            BEFORE.clear();
            EXITED.clear();
            UNREALIZED.clear();
            unread = "";
            WIRE.clear();
            STATE.clear();
            VERSION.clear();
            TURNS.clear();
            TURNED.clear();
            READ_TURNS.clear();
            MINT.clear();
            MINTED.clear();
            ATTACHED.clear();
            READ.clear();
            WROTE.clear();
        }
    }
}
