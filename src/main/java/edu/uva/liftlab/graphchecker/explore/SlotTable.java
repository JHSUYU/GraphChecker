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
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The skeleton: one slot per (interaction, world), and what contradicts it.
 *
 * <p>A SLOT is an interaction identity -- kind, producer endpoint, consumer
 * endpoint -- labelled with the WORLD (the flip set,
 * {@link ObligationFactory#worldDigest}) of the session that opened it.
 * A pairing no slot holds OPENS one; the same pairing from a later session
 * FILLS it; a pairing whose consumer is outside the closure is recorded and
 * no more.</p>
 *
 * <p>A REPLACEMENT is a WIRE consumer endpoint paired with a different
 * producer by another session IN THE SAME WORLD (DESIGN4 SS3.3c): a message
 * is paired by the run that carries it, so two pairings of one consumer
 * under the same flips mean the identity named two interactions one way,
 * and that is BLOCKING.  The same consumer paired differently in ANOTHER world is
 * growth -- the new pairing is a new arm keyed by that world -- and opens a
 * slot of its own.  A STATE reader pairs with whichever writer delivered the
 * version it read, in any world: never a replacement.</p>
 *
 * <p>ONLY AN ADMITTED REPLAY STATES A TOPOLOGY ({@link
 * SessionReader#admitted}): a session that did not run the world it was
 * asked for neither opens a slot nor contradicts one; what it paired is
 * reported DIAGNOSTIC.</p>
 */
public final class SlotTable {
    /** The file the table lives in, under the iteration directory. */
    public static final String FILE = "slots.jsonl";

    /** One interaction the skeleton holds, in one world. */
    public static final class Slot {
        public final InteractionKind kind;
        public final Endpoint producer;
        public final Endpoint consumer;
        public final String openedBySession;
        public final int openedAtWave;
        /** The world of the opening session; {@code ""} is the seed's. */
        public final String world;

        Slot(InteractionKind kind, Endpoint producer, Endpoint consumer,
             String openedBySession, int openedAtWave, String world) {
            this.kind = kind;
            this.producer = producer;
            this.consumer = consumer;
            this.openedBySession = openedBySession;
            this.openedAtWave = openedAtWave;
            this.world = world == null ? "" : world;
        }

        /** The interaction's identity, without the world. */
        public String interactionId() {
            return Interaction.of(kind, producer, consumer).id();
        }
    }

    /** What one wave's rows did to the skeleton. */
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
    /** WIRE consumer endpoint id | world -> the slot pairing it there. */
    private final Map<String, Slot> slotOfConsumer =
            new LinkedHashMap<String, Slot>();
    private boolean stated;

    SlotTable() {
    }

    /** The iteration's table, or an empty one before its first wave. */
    public static SlotTable read(Path iteration) throws IOException {
        SlotTable table = new SlotTable();
        if (iteration == null) return table;
        Path file = iteration.resolve(FILE);
        table.stated = Files.isRegularFile(file);
        for (Slot slot : RowCodec.readAll(file, ExploreCodec::readSlot)) {
            table.hold(slot);
        }
        return table;
    }

    /** Whether this iteration published a skeleton at all. */
    public boolean stated() {
        return stated;
    }

    /** Whether this consumer endpoint has a WIRE slot in any world. */
    public boolean opened(String consumerEndpointId) {
        for (Slot slot : slotOfConsumer.values()) {
            if (slot.consumer.id().equals(consumerEndpointId)) return true;
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

    private void hold(Slot slot) {
        byInteraction.put(slot.interactionId() + "|" + slot.world, slot);
        if (slot.kind == InteractionKind.WIRE) {
            slotOfConsumer.put(slot.consumer.id() + "|" + slot.world, slot);
        }
    }

    /**
     * Takes every interaction the corpus states, against this skeleton.
     *
     * @param closure the occurrence ids the anchor's closure holds: a slot is
     *                opened only for an interaction whose CONSUMER is one of
     *                them
     */
    public Reconciliation reconcile(Corpus corpus, Set<String> closure,
                                    int wave) {
        List<Slot> opened = new ArrayList<Slot>();
        List<GapRow> gaps = new ArrayList<GapRow>();
        Set<String> outside = new LinkedHashSet<String>();
        int filled = 0;
        boolean replaced = contextChanged(corpus, closure, gaps);
        for (SessionReader session : corpus.sessions()) {
            boolean authority = session.admitted();
            String world = ObligationFactory.worldDigest(
                    corpus.world(session.sessionId()));
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
                        session.sessionId(), world, authority, wave, opened,
                        gaps)) {
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
                // R-I7.1: a read that HAPPENED BEFORE the write it claims
                // to have observed contradicts the run's own order
                // (Arms.ancestor: same thread, causal anchors, thread
                // start/join).  A session's event counter alone orders
                // nothing.
                if (contradictsOrder(corpus, read, writer)) {
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
                        session.sessionId(), world, authority, wave, opened,
                        gaps)) {
                    case FILLED: filled++; break;
                    default: break;
                }
            }
        }
        return new Reconciliation(opened, filled, outside.size(), replaced,
                gaps);
    }

    /**
     * The state edges of one session that its own identities cannot separate:
     * two reads at one endpoint id (no site index) that observed DIFFERENT
     * versions of one location.  Neither opens a slot; named once.
     */
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

    /** One read's (consumer endpoint, location) pair. */
    private static String stateKey(ReadRow read) {
        return read.endpoint().id() + "|"
                + SmtLowering.locationKey(read.location());
    }

    private static boolean contradictsOrder(Corpus corpus, ReadRow read,
                                            WriteRow observed) {
        return corpus.arms().ancestor(read.endpoint(), read.seq(),
                observed.endpoint(), observed.seq(), read.sessionId());
    }

    /** One session that pairs a slot's consumer with another producer. */
    public static final class Replacement {
        public final String sessionId;
        public final String consumerEndpointId;
        public final String skeletonProducerId;
        public final String replayProducerId;
        public final String openedBySession;
        /** Whether the replacing session states this topology. */
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

        /** BLOCKING when the session states this topology, else DIAGNOSTIC. */
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

    /**
     * Every same-world replacement the corpus states: what the composition
     * asks of the skeleton, answered by the same {@link #replaced} the wave
     * decides with.
     */
    public List<Replacement> replacements(Corpus corpus) {
        List<Replacement> found = new ArrayList<Replacement>();
        if (!stated) return found;
        Set<String> seen = new LinkedHashSet<String>();
        for (SessionReader session : corpus.sessions()) {
            String world = ObligationFactory.worldDigest(
                    corpus.world(session.sessionId()));
            for (AttachRow attach : session.attaches()) {
                if (attach.producer() == null) continue;
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

    /**
     * The slot one pairing contradicts, or null: a WIRE consumer the table
     * holds against another producer IN THIS WORLD, opened by another
     * session.  A STATE pairing, a pairing the table holds, a consumer no
     * slot of this world pairs, and one session's own second pairing of a
     * consumer contradict nothing.
     */
    private Slot replaced(InteractionKind kind, Endpoint producer,
                          Endpoint consumer, String sessionId, String world) {
        if (kind != InteractionKind.WIRE) return null;
        if (byInteraction.containsKey(
                Interaction.of(kind, producer, consumer).id() + "|" + world)) {
            return null;
        }
        Slot held = slotOfConsumer.get(consumer.id() + "|" + world);
        if (held == null || held.producer.id().equals(producer.id())) {
            return null;
        }
        return held.openedBySession.equals(sessionId) ? null : held;
    }

    private enum Outcome { OPENED, FILLED, REPLACED, AMBIGUOUS, REPORTED }

    /** Appended to a row of a replay that states no topology. */
    static final String UNADMITTED =
            " (this replay was not admitted, so it states no topology)";

    /** One pair against the skeleton: grow it, fill it, or contradict it. */
    private Outcome take(InteractionKind kind, Endpoint producer,
                         Endpoint consumer, String sessionId, String world,
                         boolean authority, int wave,
                         List<Slot> opened, List<GapRow> gaps) {
        Slot slot = new Slot(kind, producer, consumer, sessionId, wave, world);
        if (byInteraction.containsKey(slot.interactionId() + "|" + world)) {
            return Outcome.FILLED;
        }
        Slot contradicted = replaced(kind, producer, consumer, sessionId,
                world);
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
        Slot held = kind == InteractionKind.WIRE
                ? slotOfConsumer.get(consumer.id() + "|" + world) : null;
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
        hold(slot);
        opened.add(slot);
        return Outcome.OPENED;
    }

    /**
     * A closure member started for a different reason than the skeleton's.
     *
     * <p>The causal context is inside an occurrence id, so a changed context
     * is an ABSENCE beside a presence: a replay ran no closure member at a
     * code point (node, region, execution index) and did run that code point
     * under another context.  Two occurrences of one code point that a
     * session ran BOTH are growth (two requests), never replacement.</p>
     *
     * <p>BLOCKING only in the world where the member ran: a replay in a
     * world no session ran the member in has grown the graph by a new
     * occurrence (DESIGN4 SS3.3a), and the row is DIAGNOSTIC.</p>
     */
    private static boolean contextChanged(Corpus corpus, Set<String> closure,
                                          List<GapRow> gaps) {
        Map<String, List<OccurrenceAddress>> byCodePoint =
                new LinkedHashMap<String, List<OccurrenceAddress>>();
        for (String id : closure) {
            OccurrenceAddress member = corpus.occurrence(id);
            if (member == null) continue;
            List<OccurrenceAddress> members = byCodePoint.get(codePoint(member));
            if (members == null) {
                members = new ArrayList<OccurrenceAddress>();
                byCodePoint.put(codePoint(member), members);
            }
            members.add(member);
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

    /** The worlds of the sessions that activated one occurrence. */
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
