package edu.uva.liftlab.graphchecker.d3.explore;

import edu.uva.liftlab.graphchecker.d3.compose.SmtLowering;
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
    /** consumer endpoint id -> the slot the skeleton pairs it in. */
    private final Map<String, Slot> slotOfConsumer =
            new LinkedHashMap<String, Slot>();

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

    /** The region slot a degraded occurrence carries: a role, not a region. */
    static final String ROLE_REGION = "ROLE.";

    public boolean holds(String interactionId) {
        return byInteraction.containsKey(interactionId);
    }

    private void hold(Slot slot) {
        byInteraction.put(slot.interactionId(), slot);
        slotOfConsumer.put(slot.consumer.id(), slot);
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
            Set<String> indistinct = indistinct(corpus, session, gaps);
            for (ReadRow read : session.reads()) {
                Endpoint consumer = read.endpoint();
                WriteRow writer = corpus.writeOf(read.sessionId(),
                        read.location(), read.observedVersion());
                if (writer == null) continue;
                // Two reads of one location at one endpoint id that observed
                // DIFFERENT versions: the session states two state edges its
                // identity cannot separate, so neither takes a slot.  Said
                // once, above, as a DIAGNOSTIC.
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
                // R-I7.1: what contradicts is not "a later version by seq"
                // -- two activations that no order relates interleave, so a
                // session's event counter alone orders nothing.  A pairing
                // contradicts the run when the read HAPPENED BEFORE the write
                // it claims to have observed, which is the one question
                // Arms.ancestor answers: same thread (one occurrence or two),
                // the causal-anchor chain, and thread start/join.
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
     * The state edges of one session that its own identities cannot separate.
     *
     * <p>A read endpoint is {@code (occurrence, site, siteIndex, attempt)}
     * and the site index is what distinguishes repeated events of one site
     * (IDENTITY-IMPL A).  A read the runtime does not stand at carries none,
     * so two reads of one field in one occurrence share an endpoint id; when
     * they observed DIFFERENT versions of that location, keying the skeleton
     * by the consumer read the run's own loop as a contradiction of itself.
     * It is not one: it is a lineage the rows cannot yet state.  Neither read
     * opens a slot -- a slot whose consumer stands for two events would offer
     * the composition an arm under the wrong path condition -- and the loss
     * is named once per endpoint and location.</p>
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

    /**
     * Whether the recorded pairing contradicts the run's own order.
     *
     * <p>Not "an earlier version by seq": two activations that no order
     * relates interleave, so a session's event counter alone orders nothing.
     * What contradicts is a read that HAPPENED BEFORE the write it claims to
     * have observed -- because its own thread wrote later, because the
     * writing activation ran on that same thread afterwards, because the
     * reader caused the writer through the message it sent, or because the
     * reader started the thread the writer ran on.  All four are the one
     * question {@code Arms.ancestor} answers, and this stage asks it rather
     * than keeping a fifth opinion about happens-before.</p>
     */
    private static boolean contradictsOrder(Corpus corpus, ReadRow read,
                                            WriteRow observed) {
        return corpus.arms().ancestor(read.endpoint(), observed.endpoint(),
                read.sessionId());
    }

    private enum Outcome { OPENED, FILLED, REPLACED, AMBIGUOUS }

    /**
     * One pair against the skeleton: grow it, fill it, or contradict it.
     *
     * <p>The decision is per SLOT.  {@code byInteraction} answers it for the
     * pair itself, and the consumer-keyed map answers the R-I6 question that
     * a slot id cannot: whether a REPLAY has paired a consumer endpoint with
     * a producer other than the one the CATALOG holds it against.  That is a
     * cross-session statement, and only that is a replacement.</p>
     *
     * <p>Two pairings of one consumer endpoint id inside ONE session are not
     * a contradiction -- a run does not contradict itself.  They are two
     * events the identity cannot yet tell apart, because an endpoint is
     * {@code (occurrence, site, siteIndex, attempt)} and a read the runtime
     * does not stand at carries no site index to separate them.  Neither
     * takes a slot, and the loss is named where a reader will see it, rather
     * than forked into an epoch that no retained set could fix.</p>
     */
    private Outcome take(InteractionKind kind, Endpoint producer,
                         Endpoint consumer, String sessionId, int wave,
                         List<Slot> opened, List<GapRow> gaps) {
        Slot slot = new Slot(kind, producer, consumer, sessionId, wave);
        String interaction = slot.interactionId();
        if (byInteraction.containsKey(interaction)) return Outcome.FILLED;
        Slot held = slotOfConsumer.get(consumer.id());
        if (held != null && !held.producer.id().equals(producer.id())) {
            if (!held.openedBySession.equals(sessionId)) {
                gaps.add(GapRow.of(sessionId, GapKind.TOPOLOGY_DIVERGENCE,
                        GapClass.BLOCKING, consumer.toString(),
                        "the catalog pairs this consumer with producer "
                                + "endpoint " + held.producer.id()
                                + ", opened by " + held.openedBySession
                                + ", and this replay pairs it with "
                                + producer.id()
                                + ": a replacement, not growth"));
                return Outcome.REPLACED;
            }
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
                // A DEGRADED occurrence's region slot is ROLE.<ROLE>: the
                // scope was lost, so the row names the role instead of a
                // region.  No such region exists in the static candidate
                // graph, so no retained set can ever grow to hold it -- SS8
                // case 2 is about a region that exists and is not retained.
                // What it states is the lineage, and that is what it says.
                if (occurrence.regionId().startsWith(ROLE_REGION)) {
                    gaps.add(GapRow.of(session.sessionId(),
                            GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                            occurrence.render(),
                            "a flipped path reached a region whose scope the "
                                    + "recording lost: " + occurrence.regionId()
                                    + " is a role, not a region of the static "
                                    + "graph, so nothing can retain it"));
                    continue;
                }
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
     * is a different id and no id-keyed test could ever see it.  What a
     * REPLACEMENT looks like from the rows is an ABSENCE beside a presence:
     * one replay did not run the closure's occurrence at all, and it DID run
     * the same code point -- the same component, region and execution index
     * -- under another context.  Then the skeleton's member is gone and
     * something else stands where it stood.</p>
     *
     * <p>Two occurrences at one code point that a session ran BOTH are
     * growth (R-I6), never replacement: the two client checksum requests of
     * one recording are two occurrences of one code point by construction,
     * and under IDENTITY-V3 every concurrent request of one entry point is.
     * Reading that as a contradiction closed the frontier of every wave and
     * proposed nothing.</p>
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
        for (SessionReader session : corpus.sessions()) {
            Set<String> ran = new LinkedHashSet<String>();
            for (ActivationRow activation : session.activations()) {
                ran.add(activation.occurrence().id());
            }
            for (ActivationRow activation : session.activations()) {
                OccurrenceAddress occurrence = activation.occurrence();
                OccurrenceAddress member =
                        byCodePoint.get(codePoint(occurrence));
                if (member == null || member.id().equals(occurrence.id())) {
                    continue;
                }
                // Both ran here: two occurrences of one code point, which is
                // what a second request IS.
                if (ran.contains(member.id())) continue;
                gaps.add(GapRow.of(session.sessionId(),
                        GapKind.TOPOLOGY_DIVERGENCE, GapClass.BLOCKING,
                        occurrence.render(),
                        "the closure holds " + member.context().render()
                                + " at this code point, this replay did not "
                                + "run it, and it ran "
                                + occurrence.context().render() + " there"));
                replaced = true;
            }
        }
        return replaced;
    }

    /** The same code point in the same control context. */
    private static String codePoint(OccurrenceAddress occurrence) {
        return occurrence.node().render() + "/" + occurrence.regionId() + "/"
                + occurrence.index().hash();
    }
}
