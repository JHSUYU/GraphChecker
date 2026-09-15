package edu.uva.liftlab.graphchecker.d3.explore;

import edu.uva.liftlab.graphchecker.d3.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.Endpoint;
import edu.uva.liftlab.graphchecker.d3.contract.GapClass;
import edu.uva.liftlab.graphchecker.d3.contract.GapKind;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.Interaction;
import edu.uva.liftlab.graphchecker.d3.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.SessionReader;
import edu.uva.liftlab.graphchecker.d3.contract.WriteRow;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The epoch's skeleton: one slot per interaction, and what may change it.
 *
 * <p>A SLOT is an interaction identity — kind, producer endpoint, consumer
 * endpoint — and the skeleton is the set of them (INTERACTION-ID R-I6, R-I7).
 * Rows from any replay, any worker, any wave fall into slots by the two
 * endpoint ids alone, which is what lets parallel workers fill them
 * independently and lets merging be per slot.</p>
 *
 * <p>Four things can happen, and only one of them is a divergence:</p>
 * <ol>
 *   <li>an interaction whose consumer is a closure member and whose pair is
 *       not in the table OPENS a slot: the skeleton grows, this replay's arm
 *       is the slot's first, and the producer's occurrence is a task of the
 *       next wave — growth is the normal case and forks nothing;</li>
 *   <li>the same pair from any later replay FILLS the slot; arms accumulate;</li>
 *   <li>an interaction outside the closure is RECORDED and no more — it is
 *       not this anchor's business, but a reader should still see it;</li>
 *   <li>a REPLACEMENT contradicts the skeleton rather than growing it: a
 *       consumer endpoint already in a slot paired with a DIFFERENT producer,
 *       a STATE reader paired with a writer outside the versions it could
 *       have observed, or a closure member whose {@code CausalContext} changed
 *       — the same code point in the same control context, started for a
 *       different reason. That is {@code TOPOLOGY_DIVERGENCE}, BLOCKING, and
 *       the campaign opens a new epoch from that replay's pairing; the old
 *       table is kept, because it is the evidence of what the epoch was.</li>
 * </ol>
 */
public final class SlotTable {
    /** The file the table lives in, under the iteration directory. */
    public static final String FILE = "slots.jsonl";

    /** One interaction the epoch's skeleton holds. */
    public static final class Slot {
        public final InteractionKind kind;
        public final Endpoint producer;
        public final Endpoint consumer;
        public final String openedBySession;
        public final int openedAtWave;

        Slot(InteractionKind kind, Endpoint producer, Endpoint consumer,
             String openedBySession, int openedAtWave) {
            this.kind = kind;
            this.producer = producer;
            this.consumer = consumer;
            this.openedBySession = openedBySession;
            this.openedAtWave = openedAtWave;
        }

        /** The slot's identity: the interaction's, and nothing else. */
        public String interactionId() {
            return Interaction.of(kind, producer, consumer).id();
        }
    }

    /** What one wave's rows did to the skeleton. */
    public static final class Reconciliation {
        public final List<Slot> opened;
        public final int filled;
        public final int outside;
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

    private final Map<String, Slot> byInteraction =
            new LinkedHashMap<String, Slot>();
    /** consumer endpoint id -> the producer the skeleton pairs it with. */
    private final Map<String, String> producerOfConsumer =
            new LinkedHashMap<String, String>();

    /** An epoch that has opened no slot yet. */
    SlotTable() {
    }

    /** The epoch's table, or an empty one before its first wave. */
    public static SlotTable read(Path iteration) throws IOException {
        SlotTable table = new SlotTable();
        if (iteration == null) return table;
        for (Slot slot : RowCodec.readAll(iteration.resolve(FILE),
                ExploreCodec::readSlot)) {
            table.hold(slot);
        }
        return table;
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

    public boolean holds(String interactionId) {
        return byInteraction.containsKey(interactionId);
    }

    private void hold(Slot slot) {
        byInteraction.put(slot.interactionId(), slot);
        producerOfConsumer.put(slot.consumer.id(), slot.producer.id());
    }

    /**
     * Takes every interaction the corpus states, against this skeleton.
     *
     * @param closure the occurrence ids the anchor's closure holds: a slot is
     *                opened only for an interaction whose CONSUMER is one of
     *                them, because a slot is a thing this anchor's failure can
     *                depend on and not every message in the recording
     * @param wave    which wave is reconciling, for the slot's own record
     */
    public Reconciliation reconcile(Corpus corpus, Set<String> closure,
                                    int wave) {
        List<Slot> opened = new ArrayList<Slot>();
        List<GapRow> gaps = new ArrayList<GapRow>();
        Set<String> outside = new LinkedHashSet<String>();
        int filled = 0;
        boolean replaced = contextChanged(corpus, closure, gaps);
        replaced |= unretained(corpus, gaps);
        for (SessionReader session : corpus.sessions()) {
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
                        session.sessionId(), wave, opened, gaps)) {
                    case FILLED: filled++; break;
                    case REPLACED: replaced = true; break;
                    default: break;
                }
            }
            for (ReadRow read : session.reads()) {
                Endpoint consumer = read.endpoint();
                WriteRow writer = corpus.writeOf(read.sessionId(),
                        read.location(), read.observedVersion());
                if (writer == null) continue;
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
                // R-I7.1: what contradicts is not "a later version by seq"
                // -- two activations of one session interleave, so seq orders
                // events only inside one of them.  A pairing contradicts the
                // run when the read observed a version its own activation
                // wrote later, or one written by an occurrence the reader
                // itself caused: a message cannot be answered before it is
                // sent.
                if (contradictsOrder(corpus, read, writer)) {
                    gaps.add(GapRow.of(session.sessionId(),
                            GapKind.TOPOLOGY_DIVERGENCE, GapClass.BLOCKING,
                            consumer.toString(),
                            "the read observed version "
                                    + read.observedVersion() + ", written by "
                                    + writer.endpoint()
                                    + ", which this run orders after the "
                                    + "read"));
                    replaced = true;
                    continue;
                }
                switch (take(InteractionKind.STATE, writer.endpoint(), consumer,
                        session.sessionId(), wave, opened, gaps)) {
                    case FILLED: filled++; break;
                    case REPLACED: replaced = true; break;
                    default: break;
                }
            }
        }
        return new Reconciliation(opened, filled, outside.size(), replaced,
                gaps);
    }

    /**
     * Whether the recorded pairing contradicts the run's own order.
     *
     * <p>Not "an earlier version by seq": two activations of one session
     * interleave, so seq orders events only INSIDE one of them.  What
     * contradicts is a read that observed a version its own activation wrote
     * later, or one written by an occurrence the reader itself caused -- a
     * message cannot be answered before it is sent.  Both are the one
     * question {@code Arms.ancestor} answers: did the READ happen before the
     * write it claims to have observed.</p>
     */
    private static boolean contradictsOrder(Corpus corpus, ReadRow read,
                                            WriteRow observed) {
        return corpus.arms().ancestor(read.endpoint(), observed.endpoint(),
                read.sessionId());
    }

    private enum Outcome { OPENED, FILLED, REPLACED }

    /** One pair against the skeleton: grow it, fill it, or contradict it. */
    private Outcome take(InteractionKind kind, Endpoint producer,
                         Endpoint consumer, String sessionId, int wave,
                         List<Slot> opened, List<GapRow> gaps) {
        Slot slot = new Slot(kind, producer, consumer, sessionId, wave);
        String interaction = slot.interactionId();
        if (byInteraction.containsKey(interaction)) return Outcome.FILLED;
        String held = producerOfConsumer.get(consumer.id());
        if (held != null && !held.equals(producer.id())) {
            gaps.add(GapRow.of(sessionId, GapKind.TOPOLOGY_DIVERGENCE,
                    GapClass.BLOCKING, consumer.toString(),
                    "this consumer is already paired with producer endpoint "
                            + held + " and this replay pairs it with "
                            + producer.id() + ": a replacement, not growth"));
            return Outcome.REPLACED;
        }
        hold(slot);
        opened.add(slot);
        return Outcome.OPENED;
    }

    /**
     * A region that ran and that this epoch cannot see inside.
     *
     * <p>INTERACTION-ID SS8 case 2: a replay reaches a region of the static
     * candidate graph that the workload never RETAINED -- the lightweight
     * entry hook publishes its activation, and the row says so
     * ({@code instrumented == false}).  That is not growth the skeleton can
     * absorb: no endpoint of that region exists, so no interaction can name
     * it and no slot can open for it.  The epoch has to be re-cut with the
     * region retained, which is the campaign's to do; this stage states the
     * fact under the name run_engine acts on.  Case 3 needs nothing: a region
     * outside the static candidate graph publishes no activation at all.</p>
     */
    private static boolean unretained(Corpus corpus, List<GapRow> gaps) {
        Set<String> named = new LinkedHashSet<String>();
        boolean divergence = false;
        for (SessionReader session : corpus.sessions()) {
            for (ActivationRow activation : session.activations()) {
                if (activation.instrumented()) continue;
                OccurrenceAddress occurrence = activation.occurrence();
                if (!named.add(occurrence.regionId())) continue;
                gaps.add(GapRow.of(session.sessionId(),
                        GapKind.TOPOLOGY_DIVERGENCE, GapClass.BLOCKING,
                        occurrence.render(),
                        "retained set must grow: " + occurrence.regionId()));
                divergence = true;
            }
        }
        return divergence;
    }

    /**
     * A closure member started for a different reason than the skeleton's.
     *
     * <p>The causal context is INSIDE an occurrence id, so a changed context
     * is a different id and no id-keyed test could ever see it.  The weaker
     * key is the one the rule means: the same component, the same region and
     * the same execution index — the same code point in the same control
     * context — carrying another context.</p>
     */
    private static boolean contextChanged(Corpus corpus, Set<String> closure,
                                          List<GapRow> gaps) {
        Map<String, OccurrenceAddress> byCodePoint =
                new LinkedHashMap<String, OccurrenceAddress>();
        for (String id : closure) {
            OccurrenceAddress member = corpus.occurrence(id);
            if (member != null) byCodePoint.put(codePoint(member), member);
        }
        boolean replaced = false;
        for (OccurrenceAddress occurrence : corpus.occurrences()) {
            OccurrenceAddress member = byCodePoint.get(codePoint(occurrence));
            if (member == null || member.id().equals(occurrence.id())) {
                continue;
            }
            gaps.add(GapRow.of("", GapKind.TOPOLOGY_DIVERGENCE,
                    GapClass.BLOCKING, occurrence.render(),
                    "the closure holds " + member.context().render()
                            + " at this code point and this replay ran it as "
                            + occurrence.context().render()));
            replaced = true;
        }
        return replaced;
    }

    /** The same code point in the same control context. */
    private static String codePoint(OccurrenceAddress occurrence) {
        return occurrence.node().render() + "/" + occurrence.regionId() + "/"
                + occurrence.index().hash();
    }
}
