package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
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
 * ({@code FocusedReplay}, {@code PAIRING_UNTAKEN}).  A native reproduction
 * is held to its plant's ORDER rows the same way, each row stating what it
 * came to ({@link RecordingPlant}).</p>
 *
 * <p>WIRE is compared at the attach, where the producer is known -- a
 * delivery into the anchor by the value that arrived too, and, where the model's arm answered the anchor by
 * its question, by its producer's question ({@link Wire#answeredBy}); STATE
 * at the close, since a writer's log is read out after the read that saw
 * it.
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
    /** A WIRE row's member: the question its producer answers, stated for a
     *  consumer of the anchor when the model's arm answered the anchor by
     *  its question ({@code explore.ConfirmMain#question}). */
    public static final String PRODUCER_QUESTION = "producerQuestion";
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
     * Writer endpoint id (or {@link #INITIAL}) and location, as "writer
     * location", -> version for a declared cell's PLACEHOLDER join; keyed by
     * writer and not by reader because the mint lands on whichever
     * occurrence reads first, and by location because an INITIAL is every
     * location's.
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
    /** A native reproduction's ORDER rows ({@link RecordingPlant}): the row
     *  number of each (after, before), as "after\nbefore". */
    private static final Map<String, Integer> PLANTED =
            new HashMap<String, Integer>();
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
     * One delivery the model chose: its producer endpoint; for a consumer
     * of the anchor, the text that must arrive (null where the model's value
     * rests on a clock, which a replay reads afresh).
     */
    private static final class Wire {
        private final String producer;
        private final String value;
        /** The question the model's producer answers, or null: its
         *  occurrence, site, site index, attempt and context shape. */
        private final OccurrenceAddress questionOccurrence;
        private final String questionSite;
        private final String questionSiteIndex;
        private final int questionAttempt;
        private final List<String> questionShape;

        private Wire(String producer, String value, JsonObject question) {
            this.producer = producer;
            this.value = value;
            this.questionOccurrence = question == null ? null
                    : OccurrenceAddress.parse(
                            optionalString(question, "occurrence"));
            this.questionSite = question == null ? ""
                    : optionalString(question, "site");
            this.questionSiteIndex = question == null ? ""
                    : optionalString(question, "siteIndex");
            this.questionAttempt = question == null ? -1
                    : question.get("attempt").getAsInt();
            List<String> shape = new ArrayList<String>();
            if (question != null && question.has("shape")) {
                for (JsonElement hop : question.getAsJsonArray("shape")) {
                    shape.add(hop.getAsString());
                }
            }
            this.questionShape = shape;
        }

        /**
         * Whether {@code producer} answers the model's producer's question:
         * the anchor is answered by its question (IDENTITY §9), so a
         * delivery into it is the model's when its producer is the same
         * site, at the same site index and attempt, of an occurrence of the
         * same region and node under a chain of the same shape over this
         * run's senders -- which turn or iteration of the chain carried it
         * is the run's timing, and only the chain's counts may differ.
         */
        private boolean answeredBy(Endpoint producer) {
            return questionOccurrence != null && producer != null
                    && questionSite.equals(producer.site())
                    && questionSiteIndex.equals(producer.siteIndex().hash())
                    && questionAttempt == producer.attempt()
                    && ContextShape.answers(producer.occurrence(),
                    questionOccurrence,
                    ScheduleLog.shape(producer.occurrence().context()),
                    questionShape);
        }
    }

    /**
     * What one delivery's comparison found, each {@code ""} when none: a
     * difference from the edge the model chose, and the substitution of
     * another producer answering the model's producer's question.
     */
    static final class Compared {
        static final Compared NOTHING = new Compared("", "");

        final String mismatch;
        final String substitution;

        private Compared(String mismatch, String substitution) {
            this.mismatch = mismatch;
            this.substitution = substitution;
        }
    }

    static boolean expected() {
        load();
        synchronized (LOCK) {
            return !WIRE.isEmpty() || !STATE.isEmpty() || !MINT.isEmpty()
                    || !BEFORE.isEmpty();
        }
    }

    /** One delivery this run paired, and the text that arrived. */
    static Compared attached(Endpoint consumer, Endpoint producer,
                             String text) {
        if (!expected() || consumer == null) return Compared.NOTHING;
        String actual = producer == null ? "" : id(producer);
        Wire chosen;
        synchronized (LOCK) {
            ATTACHED.put(id(consumer), actual);
            chosen = WIRE.get(id(consumer));
        }
        if (chosen == null) return Compared.NOTHING;
        // A Wire is never changed once read: it is compared outside the
        // monitor, where ScheduleLog's senders (a leaf) shape the producer.
        boolean substituted = !chosen.producer.equals(actual)
                && chosen.answeredBy(producer);
        List<String> differs = new ArrayList<String>();
        if (!chosen.producer.equals(actual) && !substituted) {
            differs.add("the model chose producer " + chosen.producer
                    + ", the run paired "
                    + (actual.isEmpty() ? "no export" : actual));
        }
        if (chosen.value != null && !chosen.value.equals(text)) {
            differs.add("the model's value is \"" + chosen.value
                    + "\", the run delivered "
                    + (text == null ? "none" : "\"" + text + "\""));
        }
        return new Compared(differs.isEmpty() ? ""
                : "WIRE " + id(consumer) + ": " + String.join("; ", differs),
                substituted ? "WIRE " + id(consumer) + ": the run paired "
                        + "producer " + actual + ", which answers the "
                        + "question of the model's producer "
                        + chosen.producer + " at another address" : "");
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

    /**
     * Holds an activation's entry until those ordered before it exited.  In
     * a native reproduction each ORDER row of the plant states what it came
     * to ({@link RecordingPlant#ordered}): held, waited for, or not held in
     * time.
     */
    static void entering(String activation) {
        Set<String> missing;
        synchronized (LOCK) {
            Set<String> before = BEFORE.get(activation);
            if (before == null) return;
            Set<String> waiting = new LinkedHashSet<String>(before);
            waiting.removeAll(EXITED);
            planted(RecordingPlant.HOLDING, activation, waiting);
            long timeout = Long.getLong(ORDER_TIMEOUT_PROPERTY,
                    ORDER_TIMEOUT_MS);
            long deadline = System.currentTimeMillis() + timeout;
            while (!EXITED.containsAll(before)) {
                long left = deadline - System.currentTimeMillis();
                if (left <= 0L) {
                    missing = new LinkedHashSet<String>(before);
                    missing.removeAll(EXITED);
                    UNREALIZED.add("ORDER " + activation + ": the model"
                            + " orders it after " + missing + ", which did not"
                            + " exit within " + timeout + " ms, so this"
                            + " program cannot realize the model's order");
                    Set<String> held = new LinkedHashSet<String>(before);
                    held.removeAll(missing);
                    planted(RecordingPlant.APPLIED, activation, held);
                    planted(RecordingPlant.UNHELD, activation, missing);
                    return;
                }
                try {
                    LOCK.wait(Math.min(left, 200L));
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                    return;
                }
            }
            planted(RecordingPlant.APPLIED, activation, before);
        }
    }

    /** Each plant ORDER row of {@code after} and one of {@code befores},
     *  stated as {@code event}; nothing outside a native reproduction. */
    private static void planted(String event, String after,
                                Set<String> befores) {
        for (String before : befores) {
            Integer row = PLANTED.get(after + "\n" + before);
            if (row != null) {
                RecordingPlant.ordered(event, row, after, before);
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
                String[] held = edge.getKey().split(" ", 2);
                boolean taken = false;
                List<String> observed = new ArrayList<String>();
                for (String minted : MINTED) {
                    String writer = WROTE.get(minted);
                    observed.add(minted + (writer == null ? "" : " by "
                            + writer));
                    taken |= held[0].equals(writer)
                            && minted.startsWith(held[1] + "@");
                }
                if (taken) continue;
                mismatches.add("STATE mint: the model joined a declared "
                        + "cell's placeholder of " + held[1] + " to writer "
                        + held[0] + " (version " + edge.getValue() + "), "
                        + "and no placeholder of the run observed a version "
                        + "of it that writer wrote" + (observed.isEmpty()
                        ? "" : "; the run's placeholders observed "
                        + observed));
            }
            for (Map.Entry<String, String> edge : STATE.entrySet()) {
                String observed = READ.get(edge.getKey());
                String version = VERSION.get(edge.getKey());
                // An INITIAL is what every read observes before the first
                // write: another turn's read of it says nothing of this one
                // (hdfs-bugs-slowdisk-zero SD5: the guard read the INITIAL,
                // the limit, one site at any turn, the reconfiguration's 0).
                if (!INITIAL.equals(edge.getValue())
                        && atAnotherTurn(edge.getKey(), edge.getValue())) {
                    continue;
                }
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
     * for the write reads it at whichever turn it lands.  Never asked of an
     * INITIAL, which the exact reader must observe.
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
            // A native reproduction is held to its plant's ORDER rows.
            Path file = RecordingPlant.planting()
                    ? Paths.get(RecordingPlant.file())
                    : FocusedReplay.workerFile(FILE);
            if (file == null) {
                // A CONFIRM run is handed edges, and so is a replay whose
                // world plants pairings; one that finds none beside its focus
                // row compared nothing, and says so: it is no such run.
                if (FocusedReplay.confirming() || FocusedReplay.pairs()) {
                    unread = "EDGES: this " + (FocusedReplay.confirming()
                            ? "CONFIRM run" : "replay, whose world plants "
                            + "pairings,") + " found no readable " + FILE
                            + " in its worker directory, so no edge it is"
                            + " held to was compared";
                }
                return;
            }
            try {
                for (JsonObject row : RowCodec.readJsonl(file)) {
                    String kind = optionalString(row, "kind");
                    if ("WIRE".equals(kind)) {
                        WIRE.put(optionalString(row, "consumer"), new Wire(
                                optionalString(row, "producer"),
                                stated(row, "value"),
                                row.has(PRODUCER_QUESTION)
                                        ? row.getAsJsonObject(
                                        PRODUCER_QUESTION) : null));
                    } else if ("STATE".equals(kind)
                            && row.has("mint") && !row.get("mint").isJsonNull()
                            && row.get("mint").getAsBoolean()) {
                        MINT.put(optionalString(row, "writer") + " "
                                        + optionalString(row, "location"),
                                optionalString(row, "version"));
                    } else if ("STATE".equals(kind)) {
                        String reader = optionalString(row, "reader");
                        String writer = optionalString(row, "writer");
                        String held = STATE.put(reader, writer);
                        // One read, one writer: two are no model.
                        if (held != null && !held.equals(writer)) {
                            throw new IllegalStateException("STATE_CONFLICT:"
                                    + " read " + reader + " is held to "
                                    + "writers " + held + " and " + writer);
                        }
                        VERSION.put(optionalString(row, "reader"),
                                optionalString(row, "version"));
                        String turns = stated(row, "readerAnyTurn");
                        if (turns != null) {
                            TURNS.put(optionalString(row, "reader"), turns);
                            TURNED.add(turns);
                        }
                    } else if (RecordingPlant.ORDER.equals(kind)) {
                        BEFORE.computeIfAbsent(optionalString(row, "after"),
                                key -> new LinkedHashSet<String>())
                                .add(optionalString(row, "before"));
                        if (row.has(RecordingPlant.ROW)) {
                            PLANTED.put(optionalString(row, "after") + "\n"
                                    + optionalString(row, "before"),
                                    row.get(RecordingPlant.ROW).getAsInt());
                        }
                    }
                    // MARKER and ANCHOR are checked elsewhere, and a plant's
                    // ROOT and TARGET rows by RecordingPlant.
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
                PLANTED.clear();
            }
            ordering = BEFORE.isEmpty() ? 1 : 2;
        }
    }

    public static void resetForTests() {
        synchronized (LOCK) {
            loaded = false;
            ordering = 0;
            BEFORE.clear();
            PLANTED.clear();
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
