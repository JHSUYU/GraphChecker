package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
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

public final class Confirmation {
    public static final String FILE = "expected_edges.jsonl";
    public static final String INITIAL = "INITIAL";
    public static final String PRODUCER_QUESTION = "producerQuestion";
    public static final String AFTER_ANCHOR = "afterAnchor";
    public static final String ORDER_TIMEOUT_PROPERTY =
            "causynth.confirm.order.timeout.ms";
    static final long ORDER_TIMEOUT_MS = 300000L;

    private static final Object LOCK = new Object();
    private static boolean loaded;
    private static final Map<String, Wire> WIRE =
            new LinkedHashMap<String, Wire>();
    private static final Map<String, String> MINT =
            new LinkedHashMap<String, String>();
    private static final Set<String> MINTED =
            new LinkedHashSet<String>();
    private static final Map<String, String> STATE =
            new LinkedHashMap<String, String>();
    private static final Set<String> BEHIND_ANCHOR =
            new HashSet<String>();
    private static final Map<String, String> TURNS =
            new LinkedHashMap<String, String>();
    private static final Set<String> TURNED = new HashSet<String>();
    private static final Map<String, Set<String>> READ_TURNS =
            new LinkedHashMap<String, Set<String>>();
    private static final Map<String, String> VERSION =
            new LinkedHashMap<String, String>();
    private static final Map<String, String> VIEW_AT =
            new LinkedHashMap<String, String>();
    private static final Map<String, String> ATTACHED =
            new LinkedHashMap<String, String>();
    private static final Map<String, String> READ =
            new LinkedHashMap<String, String>();
    private static final Map<String, String> WROTE =
            new LinkedHashMap<String, String>();
    private static final Map<String, Set<String>> BEFORE =
            new HashMap<String, Set<String>>();
    private static final Map<String, Integer> PLANTED =
            new HashMap<String, Integer>();
    private static final Map<String, Set<String>> CHECKED =
            new HashMap<String, Set<String>>();
    private static final Set<String> CHECK_SEEN = new HashSet<String>();
    private static final List<String> OBSERVED = new ArrayList<String>();
    private static final Set<String> EXITED = new HashSet<String>();
    private static final List<ViewHold> VIEW_HOLDS = new ArrayList<ViewHold>();
    private static final List<String> UNREALIZED = new ArrayList<String>();
    private static String unread = "";
    private static volatile boolean failFast;
    private static final AtomicBoolean ENDED_AT_MISMATCH = new AtomicBoolean();
    private static volatile int ordering;

    private Confirmation() {
    }

    private static final class Wire {
        private final String producer;
        private final String value;
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
                    || !BEFORE.isEmpty() || !CHECKED.isEmpty()
                    || !VIEW_HOLDS.isEmpty();
        }
    }

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
        boolean substituted = !chosen.producer.equals(actual)
                && chosen.answeredBy(producer);
        List<String> differs = new ArrayList<String>();
        if (!chosen.producer.equals(actual) && !substituted) {
            differs.add("the model chose producer " + chosen.producer
                    + ", the run paired "
                    + (actual.isEmpty() ? "no export" : actual));
        }
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

    public static String viewWriter(long version) {
        return VIEW_WRITER + version;
    }

    private static final String VIEW_WRITER = "VIEW@";

    public static String writer(WriteRow write) {
        return write.location().kind() == LocationKind.VIEW
                ? viewWriter(write.version())
                : write.initial() ? INITIAL : id(write.endpoint());
    }

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

    public static String id(Endpoint endpoint) {
        return endpoint.anyDelivery().id();
    }

    public static String anyTurn(Endpoint endpoint) {
        return endpoint.anyDelivery().anyTurn().id();
    }

    public static String activation(OccurrenceAddress occurrence,
                                    ExecutionIndex frames) {
        return Endpoint.activation(occurrence.anyDelivery().anyTurn(),
                frames);
    }

    public static final String CLAIM = "CLAIM ";

    public static String claim(String threadKey) {
        String key = threadKey.startsWith(ActivationRow.CLAIMED)
                ? threadKey.substring(ActivationRow.CLAIMED.length())
                : threadKey;
        String[] parts = key.split("\\|", 3);
        if (parts.length < 3) return CLAIM + key;
        CausalContext context;
        try {
            context = CausalContext.parse(parts[1]);
        } catch (IllegalArgumentException unparsed) {
            return CLAIM + key;
        }
        if (context instanceof CausalContext.Anchor) {
            context = ((CausalContext.Anchor) context).anyDelivery();
        } else if (context instanceof CausalContext.Root) {
            context = ((CausalContext.Root) context).anyTurn();
        }
        return CLAIM + parts[0] + "|" + context.render() + "|" + parts[2];
    }

    private static final int SUBMITTER_HOPS = 32;

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

    public static boolean standsUnder(OccurrenceAddress occurrence,
                                      Endpoint send,
                                      Function<String, ActivationRow> rows) {
        String sent = id(send);
        OccurrenceAddress at = occurrence;
        for (int hop = 0; hop < SUBMITTER_HOPS && at != null; hop++) {
            ActivationRow row = rows.apply(at.id());
            Endpoint producer = row == null ? null : row.anchorProducer();
            if (producer == null) return false;
            if (id(producer).equals(sent)) return true;
            at = producer.occurrence();
        }
        return false;
    }

    static boolean ordering() {
        if (ordering == 0) load();
        return ordering == 2;
    }

    static void entering(String activation) {
        synchronized (LOCK) {
            if (waited(activation)) checked(activation);
        }
    }

    private static void checked(String activation) {
        Set<String> before = CHECKED.get(activation);
        if (before == null || RecordingPlant.orderGaveWay()
                || !CHECK_SEEN.add(activation)) {
            return;
        }
        Set<String> missing = new LinkedHashSet<String>(before);
        missing.removeAll(EXITED);
        for (String first : before) {
            if (missing.contains(first)) continue;
            OBSERVED.add("ORDER " + activation + ": checked, not held, and"
                    + " observed: it entered after " + first + " exited");
            planted(RecordingPlant.OBSERVED, activation,
                    Collections.singleton(first));
        }
        if (missing.isEmpty()) return;
        UNREALIZED.add("ORDER " + activation + ": the model orders it after "
                + missing + ", which no hold realizes, so the order is"
                + " checked, and they had not exited when it entered");
        mismatched();
        planted(RecordingPlant.UNHELD, activation, missing);
        if (RecordingPlant.planting()) {
            for (String late : missing) {
                OVERDUE.add(activation + "\n" + late);
            }
            RecordingPlant.gaveWay();
        }
    }

    static List<String> observed() {
        synchronized (LOCK) {
            return new ArrayList<String>(OBSERVED);
        }
    }

    private static boolean waited(String activation) {
        Set<String> before = BEFORE.get(activation);
        if (RecordingPlant.orderGaveWay()) return false;
        if (before == null) return true;
        Set<String> waiting = new LinkedHashSet<String>(before);
        waiting.removeAll(EXITED);
        planted(RecordingPlant.HOLDING, activation, waiting);
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
                if (RecordingPlant.orderGaveWay()) return false;
                long left = deadline - System.currentTimeMillis();
                if (left <= 0L) {
                    Set<String> missing = new LinkedHashSet<String>(before);
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
                    return false;
                }
                try {
                    LOCK.wait(Math.min(left, 200L));
                } catch (InterruptedException interrupted) {
                    ENDED_WAITING.computeIfAbsent(thread,
                            key -> new ArrayList<Hold>()).add(new Hold(
                            activation, before));
                    Thread.currentThread().interrupt();
                    return false;
                }
            }
        } finally {
            WAITING.remove(thread);
            if (holding) HOLD_MOVES.incrementAndGet();
        }
        planted(RecordingPlant.APPLIED, activation, before);
        return true;
    }

    private static final AtomicLong HOLD_MOVES = new AtomicLong();

    static long holdMoves() {
        return HOLD_MOVES.get();
    }

    private static final class ViewHold {
        final String view;
        final long above;
        final String readerContext;
        final String reader;
        final String until;
        boolean readSeen;
        boolean released;
        boolean gaveWay;
        String overriddenBy;
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

    static boolean holdsViews() {
        load();
        synchronized (LOCK) {
            return !VIEW_HOLDS.isEmpty();
        }
    }

    public static String viewKey(LocationId view) {
        return view.kind() + "/" + view.owner() + "#" + view.slot();
    }

    public static String contextKey(OccurrenceAddress occurrence) {
        if (occurrence == null) return "";
        OccurrenceAddress any = occurrence.anyDelivery();
        return any.node().render() + "|" + any.context().render();
    }

    public static final String VIEW_HOLD_MAX_PROPERTY =
            "causynth.view.hold.max.ms";
    public static final String VIEW_HOLD_MAX_RECORDED_PROPERTY =
            "causynth.view.hold.max.recorded.ms";
    public static final long VIEW_HOLD_MAX_MS = 3000L;

    private static final class Deferred {
        final long version;
        final Runnable apply;
        final List<ViewHold> holds;
        final String node;
        final Object scope;
        boolean running;
        final String turn;
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

        String awaited() {
            return take ? turn : null;
        }
    }

    private static final Map<String, List<Deferred>> DEFERRED =
            new LinkedHashMap<String, List<Deferred>>();
    private static final Map<String, Thread> PUBLISHERS =
            new HashMap<String, Thread>();
    static final String PUBLISHER_THREAD = "causynth-view-publisher-";
    private static final Map<String, Object[]> APPLYING =
            new HashMap<String, Object[]>();
    private static final Set<String> BLOCKED_NAMED = new HashSet<String>();

    static boolean publishing(LocationId view, long version,
                              OccurrenceAddress at, String node,
                              Object scope, Runnable apply, String turn) {
        if (view == null || apply == null) return false;
        load();
        String key = viewKey(view);
        String queued = queueKey(view);
        String here = contextKey(at);
        if (turn != null) reached(queued, node, turn, false);
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
                    exempt = true;
                }
            }
            if (own) {
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
            OWED.get().add(begin(node, turn, due));
        }
        return deferred;
    }

    private static final class Turn {
        final String node;
        final String turn;
        final boolean take;
        final ScheduleLog.Publication publication;

        Turn(String node, String turn, boolean take,
             ScheduleLog.Publication publication) {
            this.node = node;
            this.turn = turn;
            this.take = take;
            this.publication = publication;
        }
    }

    private static final ThreadLocal<List<Turn>> OWED =
            ThreadLocal.withInitial(ArrayList::new);

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

    private static void engineFault(String turn, String step,
                                    RuntimeException fault) {
        RowRuntime.gap(GapKind.ENGINE_FAULT, GapClass.BLOCKING, turn,
                "the PUBLISH turn of " + turn + " could not be " + step
                        + ": " + fault);
    }

    static int notificationBegins() {
        return OWED.get().size();
    }

    static void notificationEnded(int mark) {
        List<Turn> owed = OWED.get();
        while (owed.size() > mark) settle(owed.remove(mark));
    }

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

    static void overridden(LocationId view, long version,
                           OccurrenceAddress at, String why) {
        if (view == null || !holdsViews()) return;
        synchronized (LOCK) {
            overriddenLocked(viewKey(view), version, at, why);
        }
    }

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

    static String queueKey(LocationId view) {
        return viewKey(view).replaceFirst("#[0-9]+$", "");
    }

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
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, key,
                    "one superseded publication was already being applied"
                            + " when the system published " + publication
                            + " at once: it may land after that"
                            + " publication");
        }
        LOCK.notifyAll();
    }

    private static long viewHoldMaxNanos() {
        return Long.getLong(VIEW_HOLD_MAX_PROPERTY, viewHoldMaxRecorded())
                * 1_000_000L;
    }

    private static long viewHoldMaxRecorded() {
        return Long.getLong(VIEW_HOLD_MAX_RECORDED_PROPERTY,
                VIEW_HOLD_MAX_MS);
    }

    private static void publish(String node) {
        try {
            publishing(node);
        } finally {
            ScheduleLog.waitsNoMore();
        }
    }

    private static void publishing(String node) {
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
                    PUBLISHERS.remove(node);
                    return;
                }
                if (due.isEmpty()) {
                    if (waiting) ScheduleLog.waitsNoMore();
                    waiting = false;
                    try {
                        LOCK.wait(wait);
                    } catch (InterruptedException interrupted) {
                    }
                    continue;
                }
            }
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
                    }
                }
                continue;
            }
            for (Object[] item : ready) {
                try {
                    apply((String) item[0], (Deferred) item[1]);
                } catch (RuntimeException | Error fault) {
                    RowRuntime.gap(GapKind.ENGINE_FAULT, GapClass.BLOCKING,
                            (String) item[0], "the view publisher of " + node
                                    + " failed applying a deferred"
                                    + " publication: " + fault);
                }
            }
        }
    }

    private static final long TURN_POLL_MS = 50L;

    private static void apply(String view, Deferred deferred) {
        synchronized (LOCK) {
            List<Deferred> queue = DEFERRED.get(view);
            if (queue == null || !queue.contains(deferred)) {
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

    static void mismatched() {
        if (!failFast || !ENDED_AT_MISMATCH.compareAndSet(false, true)) {
            return;
        }
        new Thread(ConcolicResultPublisher::concludeAtMismatch,
                "causynth-mismatch-end").start();
    }

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

    static final String VIEW_HOLD_MAX = "view-hold-max";

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

    private static final class Hold {
        final String activation;
        final Set<String> before;

        Hold(String activation, Set<String> before) {
            this.activation = activation;
            this.before = before;
        }
    }

    private static final Map<Long, Hold> WAITING = new HashMap<Long, Hold>();
    private static final Map<Long, List<Hold>> ENDED_WAITING =
            new HashMap<Long, List<Hold>>();
    private static final Set<String> RAN_ON = new LinkedHashSet<String>();

    private static void ranOn() {
        if (ENDED_WAITING.isEmpty()) return;
        List<Hold> ended = ENDED_WAITING.get(Thread.currentThread().getId());
        if (ended != null) RAN_ON.add(ended.get(ended.size() - 1).activation);
    }

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

    private static final Set<String> OVERDUE = new LinkedHashSet<String>();

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
                if (BEHIND_ANCHOR.contains(edge.getKey())) continue;
                String observed = READ.get(edge.getKey());
                String version = VERSION.get(edge.getKey());
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

    private static boolean taken(String reader, String writer,
                                 String observed) {
        String at = VIEW_AT.get(reader);
        return writer.equals(WROTE.get(observed))
                && (at == null || at.equals(observed));
    }

    private static boolean atAnotherTurn(String reader, String writer) {
        Set<String> observed = READ_TURNS.get(TURNS.get(reader));
        if (observed == null) return false;
        for (String version : observed) {
            if (writer.equals(WROTE.get(version))) return true;
        }
        return false;
    }

    private static String stated(JsonObject row, String member) {
        return row.has(member) && !row.get(member).isJsonNull()
                ? row.get(member).getAsString() : null;
    }

    static String key(LocationId location, long version) {
        return location.kind() + "/" + location.owner() + "#"
                + location.slot() + "@" + version;
    }

    private static void load() {
        synchronized (LOCK) {
            if (loaded) return;
            loaded = true;
            ordering = 1;
            Path file = RecordingPlant.planting()
                    ? Paths.get(RecordingPlant.file())
                    : FocusedReplay.workerFile(FILE);
            failFast = !RecordingPlant.planting()
                    && FocusedReplay.confirming();
            if (file == null) {
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
                        if (held != null && !held.equals(writer)) {
                            throw new IllegalStateException("STATE_CONFLICT:"
                                    + " read " + reader + " is held to "
                                    + "writers " + held + " and " + writer);
                        }
                        VERSION.put(optionalString(row, "reader"),
                                optionalString(row, "version"));
                        if (row.has(AFTER_ANCHOR)
                                && row.get(AFTER_ANCHOR).getAsBoolean()) {
                            BEHIND_ANCHOR.add(reader);
                        }
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
                        (RecordingPlant.checked(row) ? CHECKED : BEFORE)
                                .computeIfAbsent(optionalString(row, "after"),
                                key -> new LinkedHashSet<String>())
                                .add(optionalString(row, "before"));
                        if (row.has(RecordingPlant.ROW)) {
                            PLANTED.put(optionalString(row, "after") + "\n"
                                    + optionalString(row, "before"),
                                    row.get(RecordingPlant.ROW).getAsInt());
                        }
                    }
                }
            } catch (IOException | RuntimeException unreadable) {
                unread = "EDGES: " + file + " could not be read ("
                        + unreadable + "), so no edge the model chose was"
                        + " compared";
                WIRE.clear();
                STATE.clear();
                BEHIND_ANCHOR.clear();
                VERSION.clear();
                VIEW_AT.clear();
                TURNS.clear();
                TURNED.clear();
                MINT.clear();
                BEFORE.clear();
                CHECKED.clear();
                PLANTED.clear();
                VIEW_HOLDS.clear();
            }
            ordering = BEFORE.isEmpty() && CHECKED.isEmpty()
                    && VIEW_HOLDS.isEmpty() ? 1 : 2;
        }
    }
}
