package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
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

    /**
     * Lock order: this lock, then {@code ScheduleLog}'s -- a superseded
     * publication's PUBLISH turn is settled under it ({@link #superseded},
     * {@code ScheduleLog#turnNotTaken}) -- and ScheduleLog never calls this
     * class.  A turn is asked before this lock all the same, so no thread
     * holds it while it waits on the order.
     */
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
    /** A view's STATE reader endpoint id -> the (location key, version) it
     *  is held to: a view's writer ({@link #viewWriter}) names a version and
     *  no location, and a store's versions restart at every path and every
     *  life of one, so its read is taken only at that location. */
    private static final Map<String, String> VIEW_AT =
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
    /** The view holds this run is held to ({@link #publishing}). */
    private static final List<ViewHold> VIEW_HOLDS = new ArrayList<ViewHold>();
    /** The order stalls: what the model ordered and this run could not. */
    private static final List<String> UNREALIZED = new ArrayList<String>();
    /** Why this CONFIRM run's edges could not be read, or "". */
    private static String unread = "";
    /** Whether a mismatch ends this run at once ({@link #mismatched}): a
     *  CONFIRM run, never a native reproduction or an obligation replay. */
    private static volatile boolean failFast;
    private static final AtomicBoolean ENDED_AT_MISMATCH = new AtomicBoolean();
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
                    || !BEFORE.isEmpty() || !VIEW_HOLDS.isEmpty();
        }
    }

    /** One delivery this run paired, and the text that arrived. */
    static Compared attached(Endpoint consumer, Endpoint producer,
                             String text) {
        if (!expected() || consumer == null) return Compared.NOTHING;
        String actual = producer == null ? "" : id(producer);
        Wire chosen;
        synchronized (LOCK) {
            ranOn();
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
        // Each side names its nodes' run-only names by the node (the model's
        // by its arm's run, ConfirmMain#named): a node's address differs by
        // its run's port.  Exact after that: another node, or any other
        // difference, refutes.
        String delivered = text == null ? null : RunNames.name(text);
        if (chosen.value != null && !chosen.value.equals(delivered)) {
            differs.add("the model's value is \"" + chosen.value
                    + "\", the run delivered "
                    + (text == null ? "none" : "\"" + text + "\""
                            + (delivered.equals(text) ? ""
                                    : " (" + delivered + ")")));
        }
        return new Compared(differs.isEmpty() ? ""
                : "WIRE " + id(consumer) + ": " + String.join("; ", differs),
                substituted ? "WIRE " + id(consumer) + ": the run paired "
                        + "producer " + actual + ", which answers the "
                        + "question of the model's producer "
                        + chosen.producer + " at another address" : "");
    }

    /**
     * The writer a STATE row names for a node's decode of {@code version}
     * of a view (LocationKind.VIEW): decodes in work outside every selected
     * region share one endpoint, so a view's writer is its version.
     */
    public static String viewWriter(long version) {
        return VIEW_WRITER + version;
    }

    /** What every {@link #viewWriter} starts with. */
    private static final String VIEW_WRITER = "VIEW@";

    /**
     * The writer a STATE row and a world's pairing name: a view's version
     * ({@link #viewWriter}) whichever side of the window its decode stood
     * on (a view's INITIAL too: which one a version gets is the window's
     * timing), else its endpoint as {@link #id} names it, {@link #INITIAL}
     * for no occurrence's.  The one spelling CONFIRM, EXPLORE's plants and
     * COMPOSE's planted families share.
     */
    public static String writer(WriteRow write) {
        return write.location().kind() == LocationKind.VIEW
                ? viewWriter(write.version())
                : write.initial() ? INITIAL : id(write.endpoint());
    }

    /** One write row's version, by the writer {@link #writer} spells: a
     *  node's decode re-pointing its view is {@link #viewWriter}. */
    static void wrote(LocationId location, long version, Endpoint writer,
                      boolean initial) {
        if (!expected() || location == null || writer == null) return;
        synchronized (LOCK) {
            ranOn();
            WROTE.put(key(location, version),
                    location.kind() == LocationKind.VIEW
                    ? viewWriter(version) : initial ? INITIAL : id(writer));
        }
    }

    /** One read; a placeholder ({@link ReadRow#mintVersion}) is also kept. */
    static void read(Endpoint reader, LocationId location,
                     long observedVersion, long mintVersion) {
        if (!expected() || reader == null || location == null) return;
        synchronized (LOCK) {
            ranOn();
            for (ViewHold hold : VIEW_HOLDS) {
                if (hold.reader.equals(id(reader))) hold.readSeen = true;
            }
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

    /** The key CONFIRM knows one method activation by ({@link #id}): its
     *  occurrence at every delivery and every turn of a timed-wait loop
     *  ({@code OccurrenceAddress#anyTurn}, the schedule's turn family). */
    public static String activation(OccurrenceAddress occurrence,
                                    ExecutionIndex frames) {
        return Endpoint.activation(occurrence.anyDelivery().anyTurn(),
                frames);
    }

    /** How many sends {@link #submitter} follows up a chain of claimed
     *  work, as {@code Attribution} follows starters. */
    private static final int SUBMITTER_HOPS = 32;

    /**
     * Where an ORDER holds an event of {@code occurrence} so that it comes
     * after what the model orders before it ({@code explore.ConfirmMain}):
     * null where it runs ({@link ActivationRow#heldWhereItRuns}: no claimed
     * work, or a task its executor handed to a worker of its own that served
     * no queue), unless it runs as a queued task, a queue item or a
     * hand-off task that took other work on its thread ({@code
     * servingTasks}, the session's {@code SessionManifest#servingTasks}) --
     * a server's pipeline applying one request after another, a client's
     * Runner polling its update queue.  Held there it would hold every item
     * queued behind it, the writer's among them, so it is held where it was
     * sent: its anchor's producer ({@link ActivationRow#anchorProducer}, the
     * send that started the request), followed up the chain while that send
     * is itself such work.  Not its claim's START, which runs on the
     * upstream stage, a consumer too.
     *
     * @throws IllegalStateException naming the chain and the claim's kind
     *         where no send of it runs where it can be held: no hold
     *         realizes the order
     */
    public static Endpoint submitter(OccurrenceAddress occurrence,
                                     Function<String, ActivationRow> rows,
                                     Set<String> servingTasks) {
        ActivationRow row = rows.apply(occurrence.id());
        if (row == null || row.heldWhereItRuns(servingTasks)) return null;
        for (int hop = 0; hop < SUBMITTER_HOPS; hop++) {
            Endpoint send = row.anchorProducer();
            if (send == null) {
                throw new IllegalStateException("ORDER_UNHELD: "
                        + row.occurrence().render() + " runs as claimed "
                        + "work (" + row.claimedAs(servingTasks)
                        + ") and names no send of this run that started it, "
                        + "so no hold realizes an order on "
                        + occurrence.render());
            }
            ActivationRow sender = rows.apply(send.occurrence().id());
            if (sender == null || sender.heldWhereItRuns(servingTasks)) {
                return send;
            }
            row = sender;
        }
        throw new IllegalStateException("ORDER_UNHELD: past "
                + SUBMITTER_HOPS + " sends of claimed work above "
                + occurrence.render() + ", the last "
                + row.occurrence().render() + " ("
                + row.claimedAs(servingTasks) + "), no send outside one");
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
            if (before == null || RecordingPlant.orderGaveWay()) return;
            Set<String> waiting = new LinkedHashSet<String>(before);
            waiting.removeAll(EXITED);
            planted(RecordingPlant.HOLDING, activation, waiting);
            // A hold that waits is the world acting on the run
            // (FocusedReplay#worldActed), and stays in force until it ends.
            long thread = Thread.currentThread().getId();
            boolean holding = !waiting.isEmpty();
            if (holding) {
                FocusedReplay.worldActed();
                WAITING.put(thread, new Hold(activation, before));
                HOLD_MOVES.incrementAndGet();
            }
            long timeout = Long.getLong(ORDER_TIMEOUT_PROPERTY,
                    ORDER_TIMEOUT_MS);
            long deadline = System.currentTimeMillis() + timeout;
            try {
                while (!EXITED.containsAll(before)) {
                    // Another hold of a native run gave way: this one too.
                    if (RecordingPlant.orderGaveWay()) return;
                    long left = deadline - System.currentTimeMillis();
                    if (left <= 0L) {
                        missing = new LinkedHashSet<String>(before);
                        missing.removeAll(EXITED);
                        UNREALIZED.add("ORDER " + activation + ": the model"
                                + " orders it after " + missing + ", which"
                                + " did not exit within " + timeout + " ms,"
                                + " so this program cannot realize the"
                                + " model's order");
                        mismatched();
                        Set<String> held = new LinkedHashSet<String>(before);
                        held.removeAll(missing);
                        planted(RecordingPlant.APPLIED, activation, held);
                        planted(RecordingPlant.UNHELD, activation, missing);
                        if (RecordingPlant.planting()) {
                            for (String late : missing) {
                                OVERDUE.add(activation + "\n" + late);
                            }
                            RecordingPlant.gaveWay();
                        }
                        return;
                    }
                    try {
                        LOCK.wait(Math.min(left, 200L));
                    } catch (InterruptedException interrupted) {
                        // An interrupt (a cluster's shutdown) ended the
                        // wait: the hold stood until then, unless the
                        // activation goes on to do tracked work (#ranOn).
                        ENDED_WAITING.computeIfAbsent(thread,
                                key -> new ArrayList<Hold>()).add(new Hold(
                                activation, before));
                        Thread.currentThread().interrupt();
                        return;
                    }
                }
            } finally {
                WAITING.remove(thread);
                if (holding) HOLD_MOVES.incrementAndGet();
            }
            planted(RecordingPlant.APPLIED, activation, before);
        }
    }

    /** Order holds begun and ended ({@link #entering}): a replay held to
     *  the model's order waits there on purpose, up to {@link
     *  #ORDER_TIMEOUT_MS} a hold, and each hold's start and end is progress
     *  to its watch ({@code ConcolicResultPublisher#watched}). */
    private static final AtomicLong HOLD_MOVES = new AtomicLong();

    /** {@link #HOLD_MOVES}. */
    static long holdMoves() {
        return HOLD_MOVES.get();
    }

    /**
     * One VIEW_HOLD row ({@code explore.ConfirmMain#stateEdges}): a pairing
     * holds a read of a node's view to that node's decode of version {@code
     * above}, so the node's publications of the view past it are deferred
     * ({@link #publishing}) while the work that read it runs, except that
     * work's own ({@code readerContext}: its node and causal context): until
     * the reader's occurrence exits ({@code until}), or -- a read in role
     * work, which no hook closes -- until the first region that work opens
     * after the read ({@code reader}) has closed (a routed alias captures its
     * view in the request's role work and writes it in a store door's
     * region), in the run as it goes; at most VIEW_HOLD_MAX.
     */
    private static final class ViewHold {
        final String view;
        final long above;
        final String readerContext;
        final String reader;
        final String until;
        boolean readSeen;
        boolean released;
        boolean gaveWay;
        /** Who published past it before its read, or null ({@link
         *  #overridden}). */
        String overriddenBy;
        /** When it first deferred a publication (nanoTime), 0 before:
         *  what VIEW_HOLD_MAX counts from. */
        long firstDeferred;

        ViewHold(String view, long above, String readerContext,
                 String reader, String until) {
            this.view = view;
            this.above = above;
            this.readerContext = readerContext;
            this.reader = reader;
            this.until = until;
        }

        boolean ended() {
            return gaveWay || released
                    || !until.isEmpty() && EXITED.contains(until);
        }

        String label() {
            return "VIEW_HOLD " + view + " past version " + above;
        }

        String waitsFor() {
            return until.isEmpty() ? "the region read " + reader + "'s work"
                    + " opens next" : until;
        }
    }

    /**
     * Whether a hold of {@code view} can be realized: its system publishes
     * that view through the publication door ({@code
     * causynth.LibraryCatalog#publishedView}, its PUBLISHED_VIEW rows), so
     * a hold defers the publication.  A view no hook publishes (Solr's
     * legacy clusterstate.json, a snapshot's metadata) is never held: its
     * pairing is refused by name at PLAN, and at CONFIRM at any version but
     * the one its read observed (compared, held by nothing), never left to
     * give way at the bound.
     */
    public static boolean hookPublishes(LocationId view) {
        if (view == null || view.kind() != LocationKind.VIEW) return false;
        String owner = view.owner();
        int at = owner.indexOf('@');
        String path = view.slot();
        int life = path.lastIndexOf('#');
        return at > 0 && edu.uva.liftlab.graphchecker.causynth.LibraryCatalog
                .publishedView(owner.substring(0, at),
                        life < 0 ? path : path.substring(0, life));
    }

    /** Whether this run holds any view ({@link #publishing}): none, a
     *  publication is the system's alone. */
    static boolean holdsViews() {
        load();
        synchronized (LOCK) {
            return !VIEW_HOLDS.isEmpty();
        }
    }

    /** The key a VIEW_HOLD row names a node's view by. */
    public static String viewKey(LocationId view) {
        return view.kind() + "/" + view.owner() + "#" + view.slot();
    }

    /** The key a VIEW_HOLD row names a reader's work by: its node and its
     *  causal context, as every delivery of its stored message names it. */
    public static String contextKey(OccurrenceAddress occurrence) {
        if (occurrence == null) return "";
        OccurrenceAddress any = occurrence.anyDelivery();
        return any.node().render() + "|" + any.context().render();
    }

    /**
     * How long, in wall ms of this JVM, a view hold may defer a node's
     * publication of its view past the first publication it deferred: the
     * realism bound VIEW_HOLD_MAX -- a busy store-callback thread, not a lost
     * watch -- in recorded time ({@link #VIEW_HOLD_MAX_RECORDED_PROPERTY})
     * times this run's measured slowdown over the recording (run_engine.sh
     * campaign_view_hold_max: a native run's is the recorded value).  It
     * exceeds a reader's own timed poll (Solr's {@code
     * OverseerTaskProcessor} polls its queue every 2000 ms), so a reader
     * that reaches its read through its own work does within it.
     */
    public static final String VIEW_HOLD_MAX_PROPERTY =
            "causynth.view.hold.max.ms";
    /** VIEW_HOLD_MAX in recorded ms, as the case configures it
     *  (view_hold_max_ms): what a give-way row names. */
    public static final String VIEW_HOLD_MAX_RECORDED_PROPERTY =
            "causynth.view.hold.max.recorded.ms";
    /** VIEW_HOLD_MAX's recorded ms where no property states it. */
    public static final long VIEW_HOLD_MAX_MS = 3000L;

    /** One publication of a node's view deferred ({@link #publishing}). */
    private static final class Deferred {
        /** Its version; -1 a removal, -2 an update of the same version
         *  (per-replica states): neither is held, each only follows. */
        final long version;
        final Runnable apply;
        final List<ViewHold> holds;
        /** The node whose publisher applies it. */
        final String node;
        /** The scope the notification ran in, entered for its apply. */
        final Object scope;
        /** Its apply has begun (guarded by {@link #LOCK}): a supersession
         *  can no longer stop it ({@link #superseded}). */
        boolean running;
        /** Its PUBLISH turn, settled once its apply returns ({@link
         *  #settle}), or null ({@link ScheduleEvent.Kind#PUBLISH}). */
        final String turn;
        /** Whether that turn is taken -- its publisher waits until it is
         *  due -- or given up by name: an exempt version, which a pairing
         *  world puts in force whatever its turn ({@link #publishing}). */
        final boolean take;

        Deferred(long version, Runnable apply, List<ViewHold> holds,
                 String node, Object scope, String turn, boolean take) {
            this.version = version;
            this.apply = apply;
            this.holds = holds;
            this.node = node;
            this.scope = scope;
            this.turn = turn;
            this.take = take;
        }

        /** The turn its publisher waits for before it applies, or null. */
        String awaited() {
            return take ? turn : null;
        }
    }

    /** A view's queue key ({@link #queueKey}) -> its deferred publications,
     *  in the order they came: applied in that order ({@link #publish}). */
    private static final Map<String, List<Deferred>> DEFERRED =
            new LinkedHashMap<String, List<Deferred>>();
    /** Node -> the one thread applying its deferred publications. */
    private static final Map<String, Thread> PUBLISHERS =
            new HashMap<String, Thread>();
    /** A node's publisher's thread name, before the node. */
    static final String PUBLISHER_THREAD = "causynth-view-publisher-";
    /** Node -> when its publisher began the apply it runs (nanoTime), and
     *  the view's key: a blocked apply is named ({@link #blockedApplies}). */
    private static final Map<String, Object[]> APPLYING =
            new HashMap<String, Object[]>();
    /** The blocked applies already named, by node and start. */
    private static final Set<String> BLOCKED_NAMED = new HashSet<String>();

    /**
     * THE PUBLICATION HOLD (a'): a node is about to publish {@code version}
     * of its {@code view} -- make the decode the readers on the node see
     * ({@code MessageDoors#publishing}: Solr's {@code
     * ZkStateReader#updateWatchedCollection}, {@code
     * ZkStateReader.StateWatcher#refreshAndWatchChildren} and {@code
     * AliasesManager#setIfNewer}) -- on a thread delivering a store's
     * notification, outside a refresh the system asked for, at {@code at}.
     * Where a pairing holds that view below this version and the thread is
     * not the reader's own work, the publication is deferred; and once one
     * is, every later one of the view such a thread makes -- whatever its
     * version, a removal ({@code version} -1) or a same-version update (-2)
     * included -- follows it, so the node publishes in the order it would
     * have.  The reader's own work's publishes at once, as a synchronous one
     * ({@link #published}): the reader sees its own work's decode.  {@code
     * apply} runs on the node's publisher in that order, under the
     * notification's scope ({@code scope}), once every hold it waits for has
     * ended -- the reader's occurrence exited, or its role read's work
     * closed a region -- or VIEW_HOLD_MAX passed since that hold's first
     * deferral, past which the hold gives way by name.  The thread goes on:
     * Solr runs each watch callback on a pooled thread, so a slow callback
     * delays no other event, and every reader on the node keeps the version
     * it had.  A publication with a PUBLISH {@code turn} that nothing defers
     * is published by its caller, as the system would; its turn stands in
     * flight from here ({@link #begin}) and is settled when the notification's
     * callback ends ({@link #notificationEnded}), after the caller's
     * constructState -- never at the door, where what the order lets go after
     * it would read the version before it (SGF3 snapshot-no-active: the
     * Overseer's task read node0's cluster state between v8's turn and the
     * callback's constructState).
     *
     * @return whether the publication was deferred; false: the caller
     *         publishes it now
     */
    static boolean publishing(LocationId view, long version,
                              OccurrenceAddress at, String node,
                              Object scope, Runnable apply, String turn) {
        if (view == null || apply == null) return false;
        load();
        String key = viewKey(view);
        String queued = queueKey(view);
        String here = contextKey(at);
        // At its door, before its own turn is asked: the node's older
        // versions of the view not on their way will never be published
        // (ScheduleLog#publicationReached; review R3).
        if (turn != null) reached(queued, node, turn, false);
        // Its PUBLISH turn, when the order holds one not yet due, waits on
        // the node's publisher, never on this thread: a watch callback holds
        // its collection's refresh lock here.  Asked before this class's
        // lock (#LOCK).
        ScheduleLog.Stance stance = turn == null ? null
                : ScheduleLog.viewStance(node);
        boolean due = turn == null || ScheduleLog.dueNow(
                ScheduleEvent.Kind.PUBLISH, turn, stance);
        boolean deferred;
        boolean exempt = false;
        synchronized (LOCK) {
            blockedApplies();
            List<ViewHold> holding = new ArrayList<ViewHold>();
            boolean own = false;
            for (ViewHold hold : VIEW_HOLDS) {
                if (hold.ended() || !hold.view.equals(key)) continue;
                if (hold.readerContext.equals(here)) {
                    own = true;
                    break;
                }
                if (version > hold.above) {
                    holding.add(hold);
                } else {
                    // The paired version, or one before it: the pairing
                    // world puts it in force at once, whatever its turn --
                    // the reader past the cut is held by nothing, and would
                    // read the version before it.
                    exempt = true;
                }
            }
            if (own) {
                // The reader's own work: the hold never defers it, nor does
                // its turn (the reader sees its own work's decode).
                superseded(queued, version);
                holding.clear();
                exempt = true;
            }
            List<Deferred> queue = DEFERRED.get(queued);
            deferred = !holding.isEmpty() || turn != null && !due && !exempt
                    || !own && queue != null && !queue.isEmpty();
            if (deferred) {
                if (!holding.isEmpty()) FocusedReplay.worldActed();
                long now = System.nanoTime();
                for (ViewHold hold : holding) {
                    if (hold.firstDeferred == 0L) hold.firstDeferred = now;
                    planted(RecordingPlant.HOLDING, hold.label(),
                            Collections.singleton(hold.waitsFor()));
                }
                // An exempt version queued behind the view's deferred ones
                // waits for no turn: its turn is given up once it applies.
                DEFERRED.computeIfAbsent(queued,
                        unused -> new ArrayList<Deferred>())
                        .add(new Deferred(version, apply, holding, node,
                                scope, turn, !exempt));
                Thread publisher = PUBLISHERS.get(node);
                if (publisher == null || !publisher.isAlive()) {
                    publisher = new Thread(() -> publish(node),
                            PUBLISHER_THREAD + node);
                    publisher.setDaemon(true);
                    PUBLISHERS.put(node, publisher);
                    publisher.start();
                }
                LOCK.notifyAll();
            }
        }
        if (!deferred && turn != null) {
            // Due now, or exempt: its caller publishes it, and its turn is
            // settled when the callback ends -- taken where it was due at the
            // door, else given up by name.
            OWED.get().add(begin(node, turn, due));
        }
        return deferred;
    }

    /**
     * A notification's publication whose PUBLISH turn is settled once it is
     * in force: begun ({@link #begin}) where the publication starts, settled
     * ({@link #settle}) where it is in force -- after the system's own apply
     * on its node's publisher ({@link #apply}), or, published by its caller
     * on the notification's thread, when the notification's callback ends
     * ({@link #notificationEnded}: Solr's watch callbacks end right after
     * their constructState, StateWatcher#process, AliasesManager#process).
     */
    private static final class Turn {
        final String node;
        final String turn;
        /** Taken -- due where it began -- or given up by name: an exempt
         *  version, which a pairing world puts in force whatever its turn. */
        final boolean take;
        /** Its slot in flight while taken ({@code
         *  ScheduleLog#publicationBegins}), or null. */
        final ScheduleLog.Publication publication;

        Turn(String node, String turn, boolean take,
             ScheduleLog.Publication publication) {
            this.node = node;
            this.turn = turn;
            this.take = take;
            this.publication = publication;
        }
    }

    /** The turns of publications this thread's notifications made at once,
     *  settled when their callbacks end ({@link #notificationEnded}). */
    private static final ThreadLocal<List<Turn>> OWED =
            ThreadLocal.withInitial(ArrayList::new);

    /**
     * {@code turn} (null: none) of a publication on {@code node} begins:
     * taken ({@code take}), its slot stands in flight at the frontier until it
     * is settled, and a publication that waits there past a grace on a lock
     * whose owner chain reaches a thread waiting for its turn behind it has
     * its turn taken for it, named ({@code ScheduleLog#publicationBegins},
     * {@code #inFlightLocked}); one that computes or waits on anything else
     * holds its turn.  The engine's own step: a fault in it is named, never
     * thrown into the system.
     */
    private static Turn begin(String node, String turn, boolean take) {
        if (turn == null) return null;
        ScheduleLog.Publication publication = null;
        try {
            publication = take ? ScheduleLog.publicationBegins(node, turn)
                    : null;
        } catch (RuntimeException fault) {
            engineFault(turn, "began", fault);
        }
        return new Turn(node, turn, take, publication);
    }

    /**
     * {@code begun}'s publication is in force: its turn is taken ({@code
     * ScheduleLog#publicationInForce}), unless the watchdog took it for it,
     * or given up by name ({@code ScheduleLog#turnNotTaken}) -- so nothing the
     * order lets go after the turn reads past it.  The engine's own step, as
     * {@link #begin}.
     */
    private static void settle(Turn begun) {
        if (begun == null) return;
        try {
            if (begun.take) {
                ScheduleLog.publicationInForce(begun.publication, begun.node,
                        begun.turn);
            } else {
                ScheduleLog.turnNotTaken(begun.node, begun.turn, "a pairing"
                        + " world put this version in force whatever its"
                        + " recorded turn (the paired version, or the"
                        + " reader's own work's)");
            }
        } catch (RuntimeException fault) {
            engineFault(begun.turn, "settled", fault);
        }
    }

    /** A PUBLISH turn's step faulted in the engine: named, BLOCKING. */
    private static void engineFault(String turn, String step,
                                    RuntimeException fault) {
        RowRuntime.gap(GapKind.ENGINE_FAULT, GapClass.BLOCKING, turn,
                "the PUBLISH turn of " + turn + " could not be " + step
                        + ": " + fault);
    }

    /** Where a store notification's callback begins ({@code
     *  MessageDoors#notified}): the mark {@link #notificationEnded} takes. */
    static int notificationBegins() {
        return OWED.get().size();
    }

    /**
     * The store notification's callback that began at {@code mark} ended
     * ({@code MessageDoors#notified}, its finally: a throw included): every
     * publication its caller made at once is in force -- Solr's callback ends
     * after its constructState -- so their turns are settled, in the order
     * they began ({@link #settle}).
     */
    static void notificationEnded(int mark) {
        List<Turn> owed = OWED.get();
        while (owed.size() > mark) settle(owed.remove(mark));
    }

    /**
     * Version {@code site} of a view queued under {@code queued} reached
     * {@code node}'s door ({@link #publishing}; {@link #published}, {@code
     * atOnce}): its older open PUBLISH turns -- and, put in force at once,
     * its own version's -- but those of the versions deferred on the node's
     * publisher, are given up ({@code ScheduleLog#publicationReached}),
     * after this class's lock.
     */
    private static void reached(String queued, String node, String site,
                                boolean atOnce) {
        Set<Long> coming = new HashSet<Long>();
        synchronized (LOCK) {
            List<Deferred> queue = DEFERRED.get(queued);
            for (Deferred deferred : queue == null
                    ? Collections.<Deferred>emptyList() : queue) {
                if (deferred.node.equals(node)) coming.add(deferred.version);
            }
        }
        ScheduleLog.publicationReached(node, site, coming, atOnce);
    }

    /**
     * A publication the system made at once ({@code MessageDoors
     * #publishing}: no notification's, inside a refresh it asked for, or the
     * reader's own work's) of a view with publications deferred.  It read the
     * store after they did, so it supersedes the removals among them: one
     * applied after it would delete what it published.  Each deferred
     * removal and every deferral before it is dropped, named, and a removal
     * ({@code version} -1) drops them all.  The rest apply later, after it,
     * where the system's own compare (Solr's: the znode version and the
     * per-replica states' cversion) keeps the newest.  Called for every
     * such publication, a pairing's hold or none: its version is in force
     * on {@code node} at {@code site}, its PUBLISH site (null: none), and
     * the node's open turns of the view at it and older are given up
     * ({@link #reached}).
     */
    static void published(LocationId view, long version,
                          OccurrenceAddress at, String why, String node,
                          String site) {
        if (view == null) return;
        load();
        synchronized (LOCK) {
            overriddenLocked(viewKey(view), version, at, why);
            superseded(queueKey(view), version);
        }
        if (site != null) reached(queueKey(view), node, site, true);
    }

    /**
     * The system put version {@code version} of a node's view in force at
     * once ({@code at}, {@code why}): a publication no hold defers ({@link
     * #published}), or a refresh's decode that is itself what its reader
     * reads (a lazy collection's live fetch, {@code MessageDoors#decode}).
     * Each hold of that view still standing before its read, below that
     * version, is overridden: named -- a PAIRING_OVERRIDDEN row, and the
     * CONFIRM mismatch its pairing cannot be realized by -- once per hold,
     * and the read's PAIRING_UNTAKEN says who ({@link #untakenBecause}).
     * Nothing is held or released by it: the system's own refresh stands.
     * The reader's own work's publication is no override: a pairing is
     * never offered below a decode that work made before the read
     * ({@code explore.PairingFlip}), and the hold exempts it ({@link
     * #publishing}).
     */
    static void overridden(LocationId view, long version,
                           OccurrenceAddress at, String why) {
        if (view == null || !holdsViews()) return;
        synchronized (LOCK) {
            overriddenLocked(viewKey(view), version, at, why);
        }
    }

    /** {@link #overridden}, guarded by {@link #LOCK}. */
    private static void overriddenLocked(String key, long version,
                                         OccurrenceAddress at, String why) {
        for (ViewHold hold : VIEW_HOLDS) {
            if (hold.ended() || hold.readSeen || hold.overriddenBy != null
                    || !hold.view.equals(key) || version <= hold.above) {
                continue;
            }
            String where = at == null ? "a thread no occurrence runs"
                    : at.render();
            hold.overriddenBy = "version " + version + " published at once"
                    + " at " + where + " (" + why + ")";
            UNREALIZED.add(hold.label() + ": " + hold.overriddenBy
                    + " before read " + hold.reader + ": the system's own"
                    + " refresh, which no hold defers, so this program"
                    + " cannot realize the pairing");
            mismatched();
            RowRuntime.gap(GapKind.PAIRING_OVERRIDDEN, GapClass.DIAGNOSTIC,
                    key + " past version " + hold.above, "read " + hold.reader
                            + " is paired to version " + hold.above + ", and "
                            + hold.overriddenBy + " before it: the system's"
                            + " own refresh, which no hold defers");
        }
    }

    /**
     * Why the pairing of {@code reader} was not taken, as its hold knows
     * it: overridden by whom ({@link #overridden}), or given way at
     * VIEW_HOLD_MAX; "" where its hold states neither.
     */
    static String untakenBecause(String reader) {
        load();
        synchronized (LOCK) {
            for (ViewHold hold : VIEW_HOLDS) {
                if (!hold.reader.equals(reader)) continue;
                if (hold.overriddenBy != null) {
                    return "overridden: " + hold.overriddenBy;
                }
                if (hold.gaveWay) {
                    return "its hold gave way at " + VIEW_HOLD_MAX + " ("
                            + viewHoldMaxRecorded() + " ms of recorded time)";
                }
            }
            return "";
        }
    }

    /**
     * The key a view's deferred publications queue under: its {@link
     * #viewKey} without the store life its path is in ({@code
     * MessageDoors#life}, {@code #<n>}).  A system's view is per path, not
     * per life (Solr's per collection): a recreated collection's publication
     * follows the deferred ones of the collection it replaces, a removal
     * among them included, or it would apply before them and they after it
     * (review re-check 2026-10-12).
     */
    static String queueKey(LocationId view) {
        return viewKey(view).replaceFirst("#[0-9]+$", "");
    }

    /** {@link #published}, guarded by {@link #LOCK}. */
    private static void superseded(String key, long version) {
        List<Deferred> queue = DEFERRED.get(key);
        if (queue == null || queue.isEmpty()) return;
        int dropped = version == -1L ? queue.size() : 0;
        for (int i = dropped; i < queue.size(); i++) {
            if (queue.get(i).version == -1L) dropped = i + 1;
        }
        if (dropped == 0) return;
        List<Deferred> superseded = queue.subList(0, dropped);
        int running = 0;
        for (Deferred deferred : superseded) {
            if (deferred.running) running++;
            // Its turn will not be taken: settled now, by name, not left to
            // the watchdog (ScheduleLog#turnNotTaken; ScheduleLog never takes
            // this class's lock).
            if (deferred.turn != null && !deferred.running) {
                ScheduleLog.turnNotTaken(deferred.node, deferred.turn,
                        "superseded before it applied by the system's own"
                                + " publication at once");
            }
        }
        superseded.clear();
        if (queue.isEmpty()) DEFERRED.remove(key);
        String publication = version == -1L ? "a removal"
                : "version " + version;
        RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, key,
                "the system published this view at once (" + publication
                        + ") over " + dropped + " deferred publication(s) of"
                        + " it ending in a removal or older than one: they"
                        + " are dropped, superseded");
        if (running > 0) {
            // Its apply has begun outside the lock and cannot be stopped;
            // the system's own locks order it against this publication.
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, key,
                    "one superseded publication was already being applied"
                            + " when the system published " + publication
                            + " at once: it may land after that"
                            + " publication");
        }
        LOCK.notifyAll();
    }

    /** How long VIEW_HOLD_MAX is in this JVM, in nanoseconds. */
    private static long viewHoldMaxNanos() {
        return Long.getLong(VIEW_HOLD_MAX_PROPERTY, viewHoldMaxRecorded())
                * 1_000_000L;
    }

    /** VIEW_HOLD_MAX in recorded ms, as configured. */
    private static long viewHoldMaxRecorded() {
        return Long.getLong(VIEW_HOLD_MAX_RECORDED_PROPERTY,
                VIEW_HOLD_MAX_MS);
    }

    /**
     * One node's publisher: applies its views' deferred publications in the
     * order they came, each once every hold it waits for has ended or given
     * way at VIEW_HOLD_MAX (counted per hold, from its first deferral), and
     * each left at its queue's head until applied.
     * Applied outside {@link #LOCK}, under the notification's scope: {@code
     * apply} takes the system's own locks, as the notification thread would
     * have.  An interrupt never ends it; it ends once nothing of its node is
     * deferred, or a reset gave the node another.
     */
    private static void publish(String node) {
        try {
            publishing(node);
        } finally {
            // Gone: it waits for no turn (ScheduleLog#duePublications).
            ScheduleLog.waitsNoMore();
        }
    }

    /** {@link #publish}'s loop. */
    private static void publishing(String node) {
        // Whether it waits for a turn as the order's waiter.
        boolean waiting = false;
        while (true) {
            List<Object[]> due = new ArrayList<Object[]>();
            synchronized (LOCK) {
                if (PUBLISHERS.get(node) != Thread.currentThread()) return;
                long now = System.nanoTime();
                long wait = 200L;
                boolean queued = false;
                for (Map.Entry<String, List<Deferred>> view
                        : DEFERRED.entrySet()) {
                    List<Deferred> queue = view.getValue();
                    if (queue.isEmpty() || !queue.get(0).node.equals(node)) {
                        continue;
                    }
                    queued = true;
                    Deferred first = queue.get(0);
                    boolean open = false;
                    for (ViewHold hold : first.holds) {
                        if (hold.ended()) continue;
                        if (now - hold.firstDeferred >= viewHoldMaxNanos()
                                || RecordingPlant.orderGaveWay()) {
                            gaveWay(hold, first.version, view.getKey());
                        } else {
                            open = true;
                            wait = Math.max(1L, Math.min(wait,
                                    (hold.firstDeferred + viewHoldMaxNanos()
                                            - now) / 1_000_000L));
                        }
                    }
                    if (!open) due.add(new Object[] {view.getKey(), first});
                }
                if (!queued) {
                    // Nothing of its node left: the next deferral starts
                    // another (#publishing, under this lock).
                    PUBLISHERS.remove(node);
                    return;
                }
                if (due.isEmpty()) {
                    // Every head waits on a hold, none on a turn (#LOCK's
                    // order: ScheduleLog's lock under this one).
                    if (waiting) ScheduleLog.waitsNoMore();
                    waiting = false;
                    try {
                        LOCK.wait(wait);
                    } catch (InterruptedException interrupted) {
                        // Never ended by an interrupt: the queue would wait.
                    }
                    continue;
                }
            }
            // A head whose PUBLISH turn is not due waits, and only its own
            // view with it: the publisher never blocks on a turn, so another
            // view's due head is never stuck behind it -- a cross-view turn
            // cycle on one publisher (review B2: Y@3's slot before X@8's,
            // X's callback first).  It waits for them as the order's waiter,
            // where the watchdog sees it (review R1).  Asked outside this
            // class's lock.
            List<String> turns = new ArrayList<String>();
            for (Object[] item : due) {
                String turn = ((Deferred) item[1]).awaited();
                if (turn != null) turns.add(turn);
            }
            Set<String> dueTurns = turns.isEmpty()
                    ? Collections.<String>emptySet()
                    : ScheduleLog.duePublications(node, turns);
            List<Object[]> ready = new ArrayList<Object[]>();
            for (Object[] item : due) {
                Deferred deferred = (Deferred) item[1];
                if (deferred.awaited() == null
                        || dueTurns.contains(deferred.awaited())) {
                    ready.add(item);
                }
            }
            waiting = dueTurns.size() < turns.size();
            if (ready.isEmpty()) {
                synchronized (LOCK) {
                    try {
                        LOCK.wait(TURN_POLL_MS);
                    } catch (InterruptedException interrupted) {
                        // Never ended by an interrupt: the queue would wait.
                    }
                }
                continue;
            }
            for (Object[] item : ready) {
                try {
                    apply((String) item[0], (Deferred) item[1]);
                } catch (RuntimeException | Error fault) {
                    // The engine's own, never the system's (#apply names
                    // those): named, and the publisher goes on.
                    RowRuntime.gap(GapKind.ENGINE_FAULT, GapClass.BLOCKING,
                            (String) item[0], "the view publisher of " + node
                                    + " failed applying a deferred"
                                    + " publication: " + fault);
                }
            }
        }
    }

    /** How often, in ms, a publisher whose due heads all wait on their
     *  PUBLISH turns asks again. */
    private static final long TURN_POLL_MS = 50L;

    /** One deferred publication applied, under its notification's scope;
     *  what the system's code throws in it is the system's failure, named. */
    private static void apply(String view, Deferred deferred) {
        synchronized (LOCK) {
            List<Deferred> queue = DEFERRED.get(view);
            if (queue == null || !queue.contains(deferred)) {
                // Superseded after it was found due (#superseded): never
                // applied.
                return;
            }
            deferred.running = true;
            APPLYING.put(deferred.node,
                    new Object[] {System.nanoTime(), view});
        }
        long scope = MessageDoors.enterCarriedScope(deferred.scope,
                edu.uva.liftlab.graphchecker.contract.Role.EXECUTOR_TASK
                        .name(), "");
        try {
            // Its turn settled once it is in force: due already when taken
            // (#publish asked), so taken without a wait.
            Turn begun = begin(deferred.node, deferred.turn, deferred.take);
            try {
                deferred.apply.run();
            } finally {
                settle(begun);
            }
        } catch (RuntimeException | Error thrown) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, view,
                    "the system's own publication of version "
                            + deferred.version + ", deferred by a pairing's"
                            + " hold, threw " + thrown + " -- the system's"
                            + " failure, as on its notification's thread");
        } finally {
            MessageDoors.exitCarriedScope(scope);
            synchronized (LOCK) {
                APPLYING.remove(deferred.node);
                // Left at its queue's head while it applied: a publication
                // of the view meanwhile followed it (#publishing).
                List<Deferred> queue = DEFERRED.get(view);
                if (queue != null && queue.remove(deferred)
                        && queue.isEmpty()) {
                    DEFERRED.remove(view);
                }
                for (ViewHold hold : deferred.holds) {
                    if (!hold.gaveWay) {
                        planted(RecordingPlant.APPLIED, hold.label(),
                                Collections.singleton(hold.waitsFor()));
                    }
                }
                LOCK.notifyAll();
            }
        }
    }

    /**
     * The first edge the model chose that this run did not take decides a
     * CONFIRM run -- refuted, whatever the rest of it does
     * ({@code explore.ConfirmMain#decide}) -- so the run ends there, its
     * session standing with the mismatch
     * ({@code ConcolicResultPublisher#concludeAtMismatch}).  Run on, each ORDER
     * the model chose that never came stood its full timeout:
     * SGF7-bugs-snapshot-no-active's confirmation, refuted on a WIRE pairing,
     * ran 23 min at 13 % CPU.  A native reproduction counts its runs to the
     * end, and an obligation replay's untaken pairings un-admit it at its
     * close.  On a thread of its own: callers hold {@link #LOCK}.
     */
    static void mismatched() {
        if (!failFast || !ENDED_AT_MISMATCH.compareAndSet(false, true)) {
            return;
        }
        new Thread(ConcolicResultPublisher::concludeAtMismatch,
                "causynth-mismatch-end").start();
    }

    /** An apply that has run past VIEW_HOLD_MAX is named once: its node's
     *  later publications wait behind it.  Guarded by {@link #LOCK}. */
    private static void blockedApplies() {
        long now = System.nanoTime();
        for (Map.Entry<String, Object[]> applying : APPLYING.entrySet()) {
            long started = (Long) applying.getValue()[0];
            String named = applying.getKey() + "@" + started;
            if (now - started < viewHoldMaxNanos()
                    || !BLOCKED_NAMED.add(named)) {
                continue;
            }
            UNREALIZED.add("VIEW_HOLD " + applying.getValue()[1] + ": the"
                    + " deferred publication's apply on " + applying.getKey()
                    + " ran past VIEW_HOLD_MAX, so the node's later"
                    + " publications waited behind it");
            mismatched();
        }
    }

    /**
     * A hold gives way at VIEW_HOLD_MAX: unrealized by name (the run is no
     * model of the pairing: CONFIRM_MISMATCH, PAIRING_UNTAKEN), the bound
     * named for the case's {@code bounded} (run_engine.sh campaign_bounds:
     * {@code view_hold_max}), every other hold of a native run giving way
     * with it.  Guarded by {@link #LOCK}.
     */
    private static void gaveWay(ViewHold hold, long version, String view) {
        hold.gaveWay = true;
        UNREALIZED.add(hold.label() + ": the publication of version "
                + version + " was deferred VIEW_HOLD_MAX ("
                + viewHoldMaxRecorded() + " ms of recorded time, "
                + viewHoldMaxNanos() / 1_000_000L + " ms here) for "
                + hold.waitsFor() + ", which did not end, so this program"
                + " cannot realize the pairing");
        mismatched();
        planted(RecordingPlant.UNHELD, hold.label(),
                Collections.singleton(hold.waitsFor()));
        RowRuntime.gap(GapKind.BOUND_INSUFFICIENT, GapClass.DIAGNOSTIC,
                view + " " + VIEW_HOLD_MAX + "=" + viewHoldMaxRecorded(),
                "a pairing's hold of this view gave way: the reader "
                        + hold.reader + " had not read within "
                        + viewHoldMaxRecorded() + " ms of recorded time of"
                        + " the first publication it deferred");
        if (RecordingPlant.planting()) RecordingPlant.gaveWay();
    }

    /** The bound's name in a gap's subject (run_engine.sh campaign_bounds). */
    static final String VIEW_HOLD_MAX = "view-hold-max";

    /**
     * A region closed ({@code Identity#regionExit}, {@code #hopClosed}): a
     * view hold whose reader read in role work ends at the first region its
     * work closes after that read.
     */
    static void regionClosed(OccurrenceAddress occurrence) {
        if (occurrence == null || occurrence.role()) return;
        String context = contextKey(occurrence);
        synchronized (LOCK) {
            boolean released = false;
            for (ViewHold hold : VIEW_HOLDS) {
                if (hold.until.isEmpty() && hold.readSeen && !hold.released
                        && hold.readerContext.equals(context)) {
                    hold.released = true;
                    released = true;
                }
            }
            if (released) LOCK.notifyAll();
        }
    }

    /** One hold: the activation held and those ordered before it. */
    private static final class Hold {
        final String activation;
        final Set<String> before;

        Hold(String activation, Set<String> before) {
            this.activation = activation;
            this.before = before;
        }
    }

    /** Thread -> its hold, while it waits. */
    private static final Map<Long, Hold> WAITING = new HashMap<Long, Hold>();
    /** Thread -> every hold of it an interrupt ended, in order: a later
     *  hold on the thread never hides an earlier one. */
    private static final Map<Long, List<Hold>> ENDED_WAITING =
            new HashMap<Long, List<Hold>>();
    /** The activations whose interrupted hold then ran on into tracked
     *  work: their order gave way. */
    private static final Set<String> RAN_ON = new LinkedHashSet<String>();

    /** A tracked read, write or attach on this thread: if an interrupt
     *  ended a hold of it, the activation of the latest such hold ran on.
     *  Called under {@link #LOCK}. */
    private static void ranOn() {
        if (ENDED_WAITING.isEmpty()) return;
        List<Hold> ended = ENDED_WAITING.get(Thread.currentThread().getId());
        if (ended != null) RAN_ON.add(ended.get(ended.size() - 1).activation);
    }

    /**
     * How this run held its world's order, read at the close
     * ({@code FocusedReplay#refuted}): the holds that gave way (an order
     * waited out its timeout, or an interrupted hold whose activation ran
     * on into tracked work), each hold in force until the end -- still
     * waiting, or until an interrupt let it go and its activation did
     * nothing tracked after -- with the activations it waits for, and each
     * edge the run did not hold: a STATE read that observed another writer
     * than the model's, a placeholder join (MINT) whose location's
     * placeholders all observed another writer, or edges that could not be
     * read at all.  A read that never happened is none of them.
     */
    static final class Held {
        final List<String> gaveWay;
        final Map<String, Set<String>> waiting;
        final List<String> misread;

        private Held(List<String> gaveWay, Map<String, Set<String>> waiting,
                     List<String> misread) {
            this.gaveWay = gaveWay;
            this.waiting = waiting;
            this.misread = misread;
        }
    }

    static Held held() {
        load();
        synchronized (LOCK) {
            List<String> gaveWay = new ArrayList<String>(UNREALIZED);
            Map<String, Set<String>> waiting =
                    new LinkedHashMap<String, Set<String>>();
            List<Hold> holds = new ArrayList<Hold>();
            for (List<Hold> ended : ENDED_WAITING.values()) holds.addAll(ended);
            holds.addAll(WAITING.values());
            for (Hold hold : holds) {
                Set<String> missing = new LinkedHashSet<String>(hold.before);
                missing.removeAll(EXITED);
                if (missing.isEmpty()) continue;
                if (RAN_ON.contains(hold.activation)) {
                    gaveWay.add("ORDER " + hold.activation + ": an interrupt"
                            + " ended its hold and it ran on into tracked"
                            + " work before " + missing + " exited");
                } else {
                    waiting.computeIfAbsent(hold.activation,
                            key -> new LinkedHashSet<String>())
                            .addAll(missing);
                }
            }
            List<String> misread = new ArrayList<String>();
            if (!unread.isEmpty()) misread.add(unread);
            // A placeholder minted at the location, none of the writer's:
            // its read observed another (one never minted never read).
            for (Map.Entry<String, String> edge : MINT.entrySet()) {
                String[] joined = edge.getKey().split(" ", 2);
                boolean seen = false;
                boolean taken = false;
                for (String minted : MINTED) {
                    if (!minted.startsWith(joined[1] + "@")) continue;
                    seen = true;
                    taken |= joined[0].equals(WROTE.get(minted));
                }
                if (seen && !taken) {
                    misread.add("STATE mint " + joined[1] + ": no"
                            + " placeholder observed writer " + joined[0]);
                }
            }
            for (Map.Entry<String, String> edge : STATE.entrySet()) {
                String observed = READ.get(edge.getKey());
                if (observed == null
                        || taken(edge.getKey(), edge.getValue(), observed)
                        || !INITIAL.equals(edge.getValue())
                        && atAnotherTurn(edge.getKey(), edge.getValue())) {
                    continue;
                }
                misread.add("STATE " + edge.getKey() + " observed "
                        + observed + ", not writer " + edge.getValue());
            }
            return new Held(gaveWay, waiting, misread);
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
            if (!EXITED.add(activation)) return;
            LOCK.notifyAll();
            // A native run's row whose hold gave way before this exit: what
            // it waited for came, late.
            for (java.util.Iterator<String> overdue = OVERDUE.iterator();
                 overdue.hasNext();) {
                String pair = overdue.next();
                if (!pair.endsWith("\n" + activation)) continue;
                overdue.remove();
                planted(RecordingPlant.LATE, pair.substring(0,
                        pair.length() - activation.length() - 1),
                        Collections.singleton(activation));
            }
        }
    }

    /** A native run's ORDER rows whose hold gave way, as "after\nbefore":
     *  each stated {@link RecordingPlant#LATE} if its before exits. */
    private static final Set<String> OVERDUE = new LinkedHashSet<String>();

    /** Every STATE and WIRE edge the run did not take, at the close. */
    static List<String> close() {
        List<String> mismatches = new ArrayList<String>();
        boolean compared = expected();
        synchronized (LOCK) {
            if (!unread.isEmpty()) mismatches.add(unread);
            if (!compared) return mismatches;
            blockedApplies();
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
                String joined = VIEW_AT.containsKey(edge.getKey())
                        ? VIEW_AT.get(edge.getKey()) : "version " + version;
                if (observed == null) {
                    mismatches.add("STATE " + edge.getKey() + ": the model"
                            + " joined this read to writer "
                            + edge.getValue() + " (" + joined
                            + "), the run never read here");
                    continue;
                }
                if (taken(edge.getKey(), edge.getValue(), observed)) continue;
                String writer = WROTE.get(observed);
                String outside = writer == null
                        ? RowRuntime.outsideSite(observed) : null;
                mismatches.add("STATE " + edge.getKey() + ": the model"
                        + " joined this read to writer " + edge.getValue()
                        + " (" + joined + "), the run observed "
                        + observed + (writer != null ? " written by " + writer
                        : outside != null ? ", stored outside every"
                        + " activation" + (outside.isEmpty() ? ""
                        : " at " + outside) + ", which no ORDER holds"
                        : ", a version no write of this run states"));
            }
        }
        return mismatches;
    }

    /**
     * Whether the read observed what its STATE row holds it to: a version
     * the row's writer wrote, and for a view's, that version of the row's
     * location ({@link #VIEW_AT}).
     */
    private static boolean taken(String reader, String writer,
                                 String observed) {
        String at = VIEW_AT.get(reader);
        return writer.equals(WROTE.get(observed))
                && (at == null || at.equals(observed));
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
    static String key(LocationId location, long version) {
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
            failFast = !RecordingPlant.planting()
                    && FocusedReplay.confirming();
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
                        if (writer.startsWith(VIEW_WRITER)) {
                            String location = optionalString(row, "location");
                            if (location.isEmpty()) {
                                throw new IllegalStateException("STATE read "
                                        + reader + " is held to view writer "
                                        + writer + " of no location");
                            }
                            String at = location + "@"
                                    + optionalString(row, "version");
                            String other = VIEW_AT.put(reader, at);
                            if (other != null && !other.equals(at)) {
                                throw new IllegalStateException(
                                        "STATE_CONFLICT: read " + reader
                                                + " is held to " + other
                                                + " and " + at);
                            }
                        }
                        String turns = stated(row, "readerAnyTurn");
                        if (turns != null) {
                            TURNS.put(optionalString(row, "reader"), turns);
                            TURNED.add(turns);
                        }
                    } else if (RecordingPlant.VIEW_HOLD.equals(kind)) {
                        ViewHold hold = new ViewHold(
                                optionalString(row, "view"),
                                row.get("above").getAsLong(),
                                optionalString(row, "readerContext"),
                                optionalString(row, "reader"),
                                optionalString(row, "until"));
                        VIEW_HOLDS.add(hold);
                        if (row.has(RecordingPlant.ROW)) {
                            PLANTED.put(hold.label() + "\n"
                                    + hold.waitsFor(),
                                    row.get(RecordingPlant.ROW).getAsInt());
                        }
                    } else if (RecordingPlant.ORDER.equals(kind)
                            && optionalString(row, RecordingPlant.SCOPE)
                            .isEmpty()) {
                        // An event-scope row is ScheduleLog's to hold.
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
                VIEW_AT.clear();
                TURNS.clear();
                TURNED.clear();
                MINT.clear();
                BEFORE.clear();
                PLANTED.clear();
                VIEW_HOLDS.clear();
            }
            // An exit is what an ORDER row and a VIEW_HOLD both wait for:
            // the frame and region hooks report exits only while ordering.
            ordering = BEFORE.isEmpty() && VIEW_HOLDS.isEmpty() ? 1 : 2;
        }
    }

    public static void resetForTests() {
        synchronized (LOCK) {
            loaded = false;
            ordering = 0;
            BEFORE.clear();
            VIEW_HOLDS.clear();
            PLANTED.clear();
            EXITED.clear();
            OVERDUE.clear();
            UNREALIZED.clear();
            DEFERRED.clear();
            PUBLISHERS.clear();
            OWED.remove();
            APPLYING.clear();
            BLOCKED_NAMED.clear();
            WAITING.clear();
            ENDED_WAITING.clear();
            RAN_ON.clear();
            unread = "";
            WIRE.clear();
            STATE.clear();
            VERSION.clear();
            VIEW_AT.clear();
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
