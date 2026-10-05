package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.WriteRow;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The skeleton: one slot per (interaction, world), and what contradicts it.
 *
 * <p>A SLOT is (kind, producer, consumer) labelled with the opening session's
 * world ({@link ObligationFactory#worldDigest}). An unseen pairing OPENS one, a
 * repeat FILLS it, a consumer outside the closure is only recorded.</p>
 *
 * <p>A REPLACEMENT (PIPELINE §7.1) is a WIRE consumer paired with another
 * producer IN THE SAME WORLD: the schedule did not hold, BLOCKING. In another
 * world it is growth (a new slot). STATE pairings are never replacements.</p>
 *
 * <p>Only an ADMITTED replay states a topology ({@link
 * SessionReader#admitted}); others are reported DIAGNOSTIC.</p>
 *
 * <p>A slot stands on the session that opened it: one whose session left the
 * corpus holds nothing ({@link #standing}).  GROW withdraws the replay that
 * exposed a region and re-runs it under the grown plan, whose new occurrences
 * give the region's endpoints new ids; a withdrawn run's slots would pair its
 * consumers with producers no session of the corpus states, and the re-run
 * and every later session of its world would read as replacing them.</p>
 *
 * <p>An occurrence a replay answered by its shape (IDENTITY §9) stands at
 * the planned address but ran under another chain of its shape, so its
 * consumers' producers are that chain's: its pairings open slots of their
 * own beside the planned occurrence's, replace none, and are no pairing a
 * later one replaces -- whichever session lands first, and however a slot
 * file orders them, since which slots are answered is read off their opening
 * sessions ({@link #standing}).  Only another answered pairing fills such a
 * slot: a session that ran the planned address itself and pairs its
 * consumer with that chain's producer replaces the planned pairing.</p>
 */
public final class SlotTable {
    public static final String FILE = "slots.jsonl";

    /** One interaction the skeleton holds, in one world. */
    public static final class Slot {
        public final InteractionKind kind;
        public final Endpoint producer;
        public final Endpoint consumer;
        public final String openedBySession;
        public final int openedAtRound;
        /** The world of the opening session; {@code ""} is the seed's. */
        public final String world;

        Slot(InteractionKind kind, Endpoint producer, Endpoint consumer,
             String openedBySession, int openedAtRound, String world) {
            this.kind = kind;
            this.producer = producer;
            this.consumer = consumer;
            this.openedBySession = openedBySession;
            this.openedAtRound = openedAtRound;
            this.world = world == null ? "" : world;
        }

        public String interactionId() {
            return Interaction.of(kind, producer, consumer).id();
        }
    }

    public static final class Reconciliation {
        public final List<Slot> opened;
        public final int filled;
        public final int outside;
        /** Whether some admitted session contradicted a slot of its world. */
        public final boolean replaced;
        public final List<GapRow> gaps;

        private Reconciliation(List<Slot> opened, int filled, int outside,
                               boolean replaced, List<GapRow> gaps) {
            this.opened = Collections.unmodifiableList(opened);
            this.filled = filled;
            this.outside = outside;
            this.replaced = replaced;
            this.gaps = Collections.unmodifiableList(gaps);
        }
    }

    /** interaction id | world -> the slot. */
    private final Map<String, Slot> byInteraction =
            new LinkedHashMap<String, Slot>();
    /** The keys of {@link #byInteraction} an answered occurrence opened. */
    private final Set<String> answeredSlots = new HashSet<String>();
    /** WIRE consumer endpoint id | world -> the slot a later pairing of it
     *  there replaces: never one an answered occurrence opened. */
    private final Map<String, Slot> slotOfConsumer =
            new HashMap<String, Slot>();
    /** WIRE consumer endpoint id | world | session -> the slot an answered
     *  occurrence of that session opened for it. */
    private final Map<String, Slot> ownChainOf = new HashMap<String, Slot>();
    private boolean stated;

    SlotTable() {
    }

    /** The iteration's table, or an empty one before its first round. */
    public static SlotTable read(Path iteration) throws IOException {
        SlotTable table = new SlotTable();
        if (iteration == null) return table;
        Path file = iteration.resolve(FILE);
        table.stated = Files.isRegularFile(file);
        // Indexed by standing(), which knows the sessions they stand on.
        for (Slot slot : RowCodec.readAll(file, ExploreCodec::readSlot)) {
            table.byInteraction.put(key(slot), slot);
        }
        return table;
    }

    public boolean stated() {
        return stated;
    }

    /** Whether this consumer endpoint has a WIRE slot in any world. */
    public boolean opened(String consumerEndpointId) {
        for (Slot slot : byInteraction.values()) {
            if (slot.kind == InteractionKind.WIRE
                    && slot.consumer.id().equals(consumerEndpointId)) {
                return true;
            }
        }
        return false;
    }

    public void write(Path iteration) throws IOException {
        RowCodec.writeAll(iteration.resolve(FILE), slots(),
                ExploreCodec::writeSlot);
    }

    public List<Slot> slots() {
        return new ArrayList<Slot>(byInteraction.values());
    }

    public int size() {
        return byInteraction.size();
    }

    private static String key(Slot slot) {
        return slot.interactionId() + "|" + slot.world;
    }

    /** {@code answered}: the slot's consumer stands in an occurrence its
     *  opening session answered by its question ({@link
     *  SessionReader#answered}). */
    private void hold(Slot slot, boolean answered) {
        byInteraction.put(key(slot), slot);
        if (answered) {
            answeredSlots.add(key(slot));
        } else {
            answeredSlots.remove(key(slot));
        }
        if (slot.kind != InteractionKind.WIRE) return;
        if (answered) {
            ownChainOf.put(slot.consumer.id() + "|" + slot.world + "|"
                    + slot.openedBySession, slot);
        } else {
            slotOfConsumer.put(slot.consumer.id() + "|" + slot.world, slot);
        }
    }

    /**
     * Keeps the slots whose opening session is in {@code corpus}: a session
     * that left it (a GROW swap) takes its slots with it, and the session
     * standing in its place opens them again.  Each slot is indexed as its
     * opening session answered its consumer's occurrence.
     *
     * @return each session's answered occurrences, by session id
     */
    private Map<String, Set<String>> standing(Corpus corpus) {
        Map<String, Set<String>> answeredIn =
                new HashMap<String, Set<String>>();
        for (SessionReader session : corpus.sessions()) {
            answeredIn.put(session.sessionId(), session.answered());
        }
        List<Slot> held = slots();
        byInteraction.clear();
        answeredSlots.clear();
        slotOfConsumer.clear();
        ownChainOf.clear();
        for (Slot slot : held) {
            Set<String> answered = answeredIn.get(slot.openedBySession);
            if (answered == null) continue;
            hold(slot, slot.kind == InteractionKind.WIRE && answered.contains(
                    slot.consumer.occurrence().render()));
        }
        return answeredIn;
    }

    /** Takes every interaction the corpus states; only a consumer in {@code
     *  closure} opens a slot. */
    public Reconciliation reconcile(Corpus corpus, Set<String> closure,
                                    int round) {
        Map<String, Set<String>> answeredIn = standing(corpus);
        List<Slot> opened = new ArrayList<Slot>();
        List<GapRow> gaps = new ArrayList<GapRow>();
        Set<String> outside = new LinkedHashSet<String>();
        int filled = 0;
        boolean replaced = contextChanged(corpus, closure, gaps);
        for (SessionReader session : corpus.sessions()) {
            boolean authority = session.admitted();
            String world = ObligationFactory.worldDigest(
                    corpus.world(session.sessionId()));
            Set<String> answered = answeredIn.get(session.sessionId());
            for (AttachRow attach : session.attaches()) {
                if (attach.producer() == null) continue;
                Endpoint consumer = attach.endpoint();
                if (!closure.contains(consumer.occurrence().id())) {
                    if (outside.add(consumer.id())) {
                        gaps.add(GapRow.of(session.sessionId(),
                                GapKind.TOPOLOGY_DIVERGENCE,
                                GapClass.DIAGNOSTIC, consumer.toString(),
                                "an interaction outside this anchor's "
                                        + "closure: recorded, and no slot"));
                    }
                    continue;
                }
                switch (take(InteractionKind.WIRE, attach.producer(), consumer,
                        session.sessionId(), world, authority,
                        answered.contains(consumer.occurrence().render()),
                        round, opened, gaps)) {
                    case FILLED: filled++; break;
                    case REPLACED: replaced = true; break;
                    default: break;
                }
            }
            Set<String> indistinct = indistinct(corpus, session, gaps);
            for (ReadRow read : session.reads()) {
                Endpoint consumer = read.endpoint();
                WriteRow writer = corpus.writeOf(read.sessionId(),
                        read.location(), read.observedVersion());
                if (writer == null) continue;
                if (indistinct.contains(stateKey(read))) continue;
                if (!closure.contains(consumer.occurrence().id())) {
                    if (outside.add(consumer.id())) {
                        gaps.add(GapRow.of(session.sessionId(),
                                GapKind.TOPOLOGY_DIVERGENCE,
                                GapClass.DIAGNOSTIC, consumer.toString(),
                                "a state edge outside this anchor's closure: "
                                        + "recorded, and no slot"));
                    }
                    continue;
                }
                // PIPELINE §7.1: a read happening before the write it claims to
                // observe contradicts the run's order.
                if (contradictsOrder(read, writer)) {
                    gaps.add(GapRow.of(session.sessionId(),
                            GapKind.TOPOLOGY_DIVERGENCE,
                            authority ? GapClass.BLOCKING
                                    : GapClass.DIAGNOSTIC,
                            consumer.toString(),
                            "the read observed version "
                                    + read.observedVersion() + ", written by "
                                    + writer.endpoint()
                                    + ", which this run orders after the "
                                    + "read" + (authority ? "" : UNADMITTED)));
                    replaced |= authority;
                    continue;
                }
                switch (take(InteractionKind.STATE, writer.endpoint(), consumer,
                        session.sessionId(), world, authority, false, round,
                        opened, gaps)) {
                    case FILLED: filled++; break;
                    default: break;
                }
            }
        }
        return new Reconciliation(opened, filled, outside.size(), replaced,
                gaps);
    }

    /** Reads one endpoint id cannot separate (same id, different versions of
     *  one location); named once, no slot. */
    private static Set<String> indistinct(Corpus corpus,
                                          SessionReader session,
                                          List<GapRow> gaps) {
        Map<String, Long> first = new LinkedHashMap<String, Long>();
        Set<String> found = new LinkedHashSet<String>();
        for (ReadRow read : session.reads()) {
            if (corpus.writeOf(read.sessionId(), read.location(),
                    read.observedVersion()) == null) {
                continue;
            }
            String key = stateKey(read);
            Long seen = first.get(key);
            if (seen == null) {
                first.put(key, read.observedVersion());
                continue;
            }
            if (seen.longValue() == read.observedVersion()) continue;
            if (!found.add(key)) continue;
            gaps.add(GapRow.of(session.sessionId(), GapKind.LINEAGE_LOST,
                    GapClass.DIAGNOSTIC, read.endpoint().toString(),
                    "site index missing: two reads of "
                            + read.endpoint().site() + " in "
                            + read.endpoint().occurrence().render()
                            + " observe v" + seen + " and v"
                            + read.observedVersion()
                            + " of the same location, so this session states "
                            + "two state edges one endpoint id cannot tell "
                            + "apart; neither opens a slot"));
        }
        return found;
    }

    private static String stateKey(ReadRow read) {
        return read.endpoint().id() + "|"
                + SmtLowering.locationKey(read.location());
    }

    /**
     * Whether this run read before the write it claims to have observed.
     * Both rows' seqs are the VM's one event clock of the session
     * (CONTRACT-SPEC §2.2), so they order the two whatever thread ran
     * them; a row the clock did not number (seq 0) orders nothing.  Never
     * the anchor chain: an occurrence goes on after the message it sent,
     * and hdfs-11741 r3's balancer dispatcher read the delay its own move
     * task had written a turn before (32 BLOCKING rows).
     */
    private static boolean contradictsOrder(ReadRow read,
                                            WriteRow observed) {
        return read.seq() > 0L && observed.seq() > 0L
                && read.seq() < observed.seq();
    }

    /** One session that pairs a slot's consumer with another producer. */
    public static final class Replacement {
        public final String sessionId;
        public final String consumerEndpointId;
        public final String skeletonProducerId;
        public final String replayProducerId;
        public final String openedBySession;
        public final boolean admitted;

        Replacement(String sessionId, String consumerEndpointId,
                    String skeletonProducerId, String replayProducerId,
                    String openedBySession, boolean admitted) {
            this.sessionId = sessionId;
            this.consumerEndpointId = consumerEndpointId;
            this.skeletonProducerId = skeletonProducerId;
            this.replayProducerId = replayProducerId;
            this.openedBySession = openedBySession;
            this.admitted = admitted;
        }

        public GapClass cls() {
            return admitted ? GapClass.BLOCKING : GapClass.DIAGNOSTIC;
        }

        public String detail() {
            return "the skeleton pairs consumer " + consumerEndpointId
                    + " with producer " + skeletonProducerId + " (slot opened"
                    + " by session " + openedBySession + ") and session "
                    + sessionId + " paired it with producer "
                    + replayProducerId + " in the same world: two pairings"
                    + " of one consumer under the same flips are a"
                    + " replacement, not growth, so this iteration's"
                    + " families take no rows from that session"
                    + (admitted ? "" : UNADMITTED);
        }
    }

    /** Every same-world replacement the corpus states, by the same {@link
     *  #replaced} rule. */
    public List<Replacement> replacements(Corpus corpus) {
        List<Replacement> found = new ArrayList<Replacement>();
        if (!stated) return found;
        Map<String, Set<String>> answeredIn = standing(corpus);
        Set<String> seen = new LinkedHashSet<String>();
        for (SessionReader session : corpus.sessions()) {
            String world = ObligationFactory.worldDigest(
                    corpus.world(session.sessionId()));
            Set<String> answered = answeredIn.get(session.sessionId());
            for (AttachRow attach : session.attaches()) {
                if (attach.producer() == null) continue;
                if (answered.contains(
                        attach.endpoint().occurrence().render())) {
                    continue;
                }
                Slot held = replaced(InteractionKind.WIRE, attach.producer(),
                        attach.endpoint(), session.sessionId(), world);
                if (held == null) continue;
                if (!seen.add(session.sessionId() + "|"
                        + attach.endpoint().id())) {
                    continue;
                }
                found.add(new Replacement(session.sessionId(),
                        attach.endpoint().id(), held.producer.id(),
                        attach.producer().id(), held.openedBySession,
                        session.admitted()));
            }
        }
        return found;
    }

    /** The slot this pairing, of an occurrence its session did not answer
     *  by its question, contradicts: same-world WIRE consumer, other
     *  producer, other session. */
    private Slot replaced(InteractionKind kind, Endpoint producer,
                          Endpoint consumer, String sessionId, String world) {
        if (kind != InteractionKind.WIRE) return null;
        if (holds(Interaction.of(kind, producer, consumer).id() + "|" + world,
                false)) {
            return null;
        }
        Slot held = slotOfConsumer.get(consumer.id() + "|" + world);
        if (held == null || held.producer.id().equals(producer.id())) {
            return null;
        }
        return held.openedBySession.equals(sessionId) ? null : held;
    }

    /** Whether a slot holds this pairing: one an answered occurrence opened
     *  holds an answered pairing only. */
    private boolean holds(String key, boolean answered) {
        return byInteraction.containsKey(key)
                && (answered || !answeredSlots.contains(key));
    }

    private enum Outcome { OPENED, FILLED, REPLACED, AMBIGUOUS, REPORTED }

    static final String UNADMITTED =
            " (this replay was not admitted, so it states no topology)";

    /**
     * One pair against the skeleton: grow it, fill it, or contradict it.
     * {@code answered}: the consumer stands in an occurrence its session
     * answered by its question ({@link SessionReader#answered}), whose
     * pairing is its own chain's: growth, never a replacement of the
     * declared one's.
     */
    private Outcome take(InteractionKind kind, Endpoint producer,
                         Endpoint consumer, String sessionId, String world,
                         boolean authority, boolean answered, int round,
                         List<Slot> opened, List<GapRow> gaps) {
        Slot slot = new Slot(kind, producer, consumer, sessionId, round, world);
        if (holds(key(slot), answered)) return Outcome.FILLED;
        Slot contradicted = answered ? null
                : replaced(kind, producer, consumer, sessionId, world);
        if (contradicted != null) {
            gaps.add(GapRow.of(sessionId, GapKind.TOPOLOGY_DIVERGENCE,
                    authority ? GapClass.BLOCKING : GapClass.DIAGNOSTIC,
                    consumer.toString(),
                    "the catalog pairs this consumer with producer "
                            + "endpoint " + contradicted.producer.id()
                            + ", opened by " + contradicted.openedBySession
                            + " in the same world, and this replay pairs it "
                            + "with " + producer.id()
                            + ": a replacement, not growth"
                            + (authority ? "" : UNADMITTED)));
            return authority ? Outcome.REPLACED : Outcome.REPORTED;
        }
        if (!authority) {
            gaps.add(GapRow.of(sessionId, GapKind.TOPOLOGY_DIVERGENCE,
                    GapClass.DIAGNOSTIC, consumer.toString(),
                    "this replay pairs this consumer with producer endpoint "
                            + producer.id() + ", which the skeleton does not "
                            + "hold in its world, and no slot is opened for it"
                            + UNADMITTED));
            return Outcome.REPORTED;
        }
        Slot held = kind != InteractionKind.WIRE ? null : answered
                ? ownChainOf.get(consumer.id() + "|" + world + "|" + sessionId)
                : slotOfConsumer.get(consumer.id() + "|" + world);
        if (held != null && !held.producer.id().equals(producer.id())) {
            gaps.add(GapRow.of(sessionId, GapKind.LINEAGE_LOST,
                    GapClass.DIAGNOSTIC, consumer.toString(),
                    "site index missing: this one session pairs this consumer "
                            + "endpoint with producer endpoints "
                            + held.producer.id() + " and " + producer.id()
                            + ", so its events cannot be told apart and "
                            + "neither opens a slot"));
            return Outcome.AMBIGUOUS;
        }
        hold(slot, answered);
        opened.add(slot);
        return Outcome.OPENED;
    }

    /**
     * A closure member that ran under a different causal context. The context
     * is part of the occurrence id, so this is an absence beside a presence at
     * one code point; a session running BOTH is growth (two requests). BLOCKING
     * only in a world where the member ran; elsewhere a new occurrence.
     */
    private static boolean contextChanged(Corpus corpus, Set<String> closure,
                                          List<GapRow> gaps) {
        Map<String, List<OccurrenceAddress>> byCodePoint =
                new LinkedHashMap<String, List<OccurrenceAddress>>();
        for (String id : closure) {
            OccurrenceAddress member = corpus.occurrence(id);
            if (member == null) continue;
            byCodePoint.computeIfAbsent(codePoint(member),
                    key -> new ArrayList<OccurrenceAddress>()).add(member);
        }
        boolean replaced = false;
        for (SessionReader session : corpus.sessions()) {
            boolean authority = session.admitted();
            String world = ObligationFactory.worldDigest(
                    corpus.world(session.sessionId()));
            Set<String> ran = new LinkedHashSet<String>();
            for (ActivationRow activation : session.activations()) {
                ran.add(activation.occurrence().id());
            }
            for (ActivationRow activation : session.activations()) {
                OccurrenceAddress occurrence = activation.occurrence();
                List<OccurrenceAddress> members =
                        byCodePoint.get(codePoint(occurrence));
                if (members == null || closure.contains(occurrence.id())) {
                    continue;
                }
                boolean memberRan = false;
                boolean sameWorld = false;
                StringBuilder held = new StringBuilder();
                for (OccurrenceAddress member : members) {
                    memberRan |= ran.contains(member.id());
                    sameWorld |= worldsRunning(corpus, member).contains(world);
                    if (held.length() > 0) held.append(", ");
                    held.append(member.context().render());
                }
                if (memberRan) continue;
                boolean blocking = authority && sameWorld;
                gaps.add(GapRow.of(session.sessionId(),
                        GapKind.TOPOLOGY_DIVERGENCE,
                        blocking ? GapClass.BLOCKING : GapClass.DIAGNOSTIC,
                        occurrence.render(),
                        "the closure holds " + held
                                + " at this code point, and this replay ran "
                                + "it only under "
                                + occurrence.context().render()
                                + (sameWorld ? "" : " (in a world no session "
                                + "ran the member in: a new occurrence, not a "
                                + "replacement)")
                                + (authority ? "" : UNADMITTED)));
                replaced |= blocking;
            }
        }
        return replaced;
    }

    private static Set<String> worldsRunning(Corpus corpus,
                                             OccurrenceAddress occurrence) {
        Set<String> worlds = new LinkedHashSet<String>();
        for (SessionReader session : corpus.sessions()) {
            if (corpus.activation(session.sessionId(), occurrence) != null) {
                worlds.add(ObligationFactory.worldDigest(
                        corpus.world(session.sessionId())));
            }
        }
        return worlds;
    }

    /** The same code point in the same control context. */
    private static String codePoint(OccurrenceAddress occurrence) {
        return occurrence.node().render() + "/" + occurrence.regionId() + "/"
                + occurrence.index().hash();
    }
}
