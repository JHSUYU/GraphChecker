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
 *   <li>a REPLACEMENT contradicts the skeleton rather than growing it: a WIRE
 *       consumer endpoint already in a slot paired with a DIFFERENT producer
 *       by another session, a STATE reader paired with a writer outside the
 *       versions it could have observed, or a closure member whose
 *       {@code CausalContext} changed
 *       — the same code point in the same control context, started for a
 *       different reason. That is {@code TOPOLOGY_DIVERGENCE}, BLOCKING, and
 *       the campaign opens a new epoch from that replay's pairing; the old
 *       table is kept, because it is the evidence of what the epoch was.</li>
 * </ol>
 *
 * <p>ONLY AN ADMITTED REPLAY STATES A TOPOLOGY. All four are statements a
 * SESSION makes about the world this epoch runs, and a session states them
 * only when its own result rows admit every obligation it ran ({@link
 * SessionReader#admitted}; a seed is asked nothing and is always an
 * authority). A replay that did not run the world it was asked for neither
 * opens a slot nor contradicts one: what it paired is reported {@code
 * TOPOLOGY_DIVERGENCE} DIAGNOSTIC, the skeleton is unchanged, and the wave
 * goes on. hdfs-11741 campaign #2 is why: one NOT_ADMITTED replay, whose
 * mint had planted no clock skew, paired eight consumers with producers the
 * skeleton does not carry, and the campaign stopped on a world no replay had
 * run.</p>
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
    /**
     * WIRE consumer endpoint id -> the slot the skeleton pairs it in.
     *
     * <p>WIRE only, and that is the whole of R-I6 vs R-I7: a message has ONE
     * producer, so a consumer endpoint the catalog pairs with another one is
     * a contradiction -- the routing, the retry or the binding changed.  A
     * STATE reader has no such thing.  Which writer delivered the version it
     * read is a fact about that session's path, and across sessions the
     * writers ARE the family's arms; a flip is expected to change which one
     * delivers, because that is what the flip is for.  17960's counter read
     * pairs with createSnapshot in the seed and with deleteSnapshot in every
     * marker flip, and reading that as a replacement forked an epoch over
     * the arm the wave had just asked for.  So "opened by another session"
     * means nothing for a STATE slot: it is never consulted, and a STATE
     * pairing no slot holds is growth.</p>
     */
    private final Map<String, Slot> slotOfConsumer =
            new LinkedHashMap<String, Slot>();

    /**
     * Whether this epoch published a table at all.
     *
     * <p>An epoch that has published none has opened no slots, and every
     * pairing in the rows is then growth: the rule has nothing to
     * contradict, so a reader says nothing at all rather than naming every
     * interaction of the recording as unopened.</p>
     */
    private boolean stated;

    /** An epoch that has opened no slot yet. */
    SlotTable() {
    }

    /** The epoch's table, or an empty one before its first wave. */
    public static SlotTable read(Path iteration) throws IOException {
        SlotTable table = new SlotTable();
        if (iteration == null) return table;
        Path file = iteration.resolve(FILE);
        table.stated = Files.isRegularFile(file);
        // The codec refuses a row it cannot read rather than skipping it: a
        // slot whose kind or whose endpoints do not parse is a skeleton this
        // stage cannot state, and dropping it in silence would read as
        // "no slot here", which is the one answer that means growth.
        for (Slot slot : RowCodec.readAll(file, ExploreCodec::readSlot)) {
            table.hold(slot);
        }
        return table;
    }

    /** Whether this epoch published a skeleton at all. */
    public boolean stated() {
        return stated;
    }

    /** Whether this consumer endpoint has a WIRE slot in the skeleton. */
    public boolean opened(String consumerEndpointId) {
        return slotOfConsumer.containsKey(consumerEndpointId);
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

    private void hold(Slot slot) {
        byInteraction.put(slot.interactionId(), slot);
        if (slot.kind == InteractionKind.WIRE) {
            slotOfConsumer.put(slot.consumer.id(), slot);
        }
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
            // ONLY AN ADMITTED REPLAY STATES A TOPOLOGY ({@link
            // SessionReader#admitted}).  A session that did not run the
            // world it was asked for neither grows this skeleton nor
            // contradicts it: what it paired is REPORTED, DIAGNOSTIC, and
            // the wave goes on planning from the skeleton it has.
            boolean authority = session.admitted();
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
                        session.sessionId(), authority, wave, opened, gaps)) {
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
                // No REPLACED case: a state pairing cannot contradict the
                // catalog, so take() never answers one for a STATE slot.
                switch (take(InteractionKind.STATE, writer.endpoint(), consumer,
                        session.sessionId(), authority, wave, opened, gaps)) {
                    case FILLED: filled++; break;
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
     *
     * <p>The two EVENTS are these two rows, and each carries the seq it
     * happened at; the endpoints alone do not, because a site the runtime
     * does not stand at has no site index and one endpoint id then names
     * every event of that site in its occurrence.</p>
     */
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
        /**
         * Whether the replacing session STATES this topology.
         *
         * <p>{@link SessionReader#admitted}, read where the session is in
         * hand.  The arms are held out either way -- the two pairings
         * cannot both be this epoch's -- and what changes is whether the
         * row STOPS the composition: a replay that did not run the world
         * it was asked for contradicts nothing.</p>
         */
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

        /** Both pairings, which is what the gap has to name. */
        public String detail() {
            return "the skeleton pairs consumer " + consumerEndpointId
                    + " with producer " + skeletonProducerId + " (slot opened"
                    + " by session " + openedBySession + ") and session "
                    + sessionId + " paired it with producer "
                    + replayProducerId + ": two pairings of one consumer are"
                    + " a replacement, not growth, so this epoch's families"
                    + " take no rows from that session"
                    + (admitted ? "" : UNADMITTED);
        }
    }

    /**
     * Every replacement the corpus states, in session order.
     *
     * <p>What the COMPOSITION asks of the skeleton: a replacing session's
     * rows must not fill this epoch's families, because the two pairings
     * cannot both be this epoch's.  Asked of the attach rows and nothing
     * else -- the pairing is a recorded fact of the run that made it, and a
     * replacement is two runs disagreeing about it -- and answered by
     * {@link #replaced}, the same predicate {@link #take} decides a wave
     * with, so the composition cannot hold a second opinion about what
     * contradicts the epoch.</p>
     */
    public List<Replacement> replacements(Corpus corpus) {
        List<Replacement> found = new ArrayList<Replacement>();
        if (!stated) return found;
        Set<String> seen = new LinkedHashSet<String>();
        for (SessionReader session : corpus.sessions()) {
            for (AttachRow attach : session.attaches()) {
                if (attach.producer() == null) continue;
                Slot held = replaced(InteractionKind.WIRE, attach.producer(),
                        attach.endpoint(), session.sessionId());
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
     * The slot one pairing CONTRADICTS, or null when it contradicts none.
     *
     * <p>R-I6, in one place.  A pairing the table already holds FILLS its
     * slot; a WIRE consumer the table holds against another producer, by
     * another session, is a REPLACEMENT; a STATE pairing contradicts
     * nothing (R-I7/R-I7.1: the writers different sessions delivered from
     * ARE the family's arms); and one run's own second pairing of one
     * consumer endpoint is not a contradiction either -- a run does not
     * contradict itself -- but a lineage its endpoint ids cannot state.</p>
     */
    private Slot replaced(InteractionKind kind, Endpoint producer,
                          Endpoint consumer, String sessionId) {
        if (kind != InteractionKind.WIRE) return null;
        if (byInteraction.containsKey(
                Interaction.of(kind, producer, consumer).id())) {
            return null;
        }
        Slot held = slotOfConsumer.get(consumer.id());
        if (held == null || held.producer.id().equals(producer.id())) {
            return null;
        }
        return held.openedBySession.equals(sessionId) ? null : held;
    }

    private enum Outcome { OPENED, FILLED, REPLACED, AMBIGUOUS, REPORTED }

    /**
     * What a topology statement of a replay that was not admitted says.
     *
     * <p>Appended to the row's own detail, so a reader sees the pairing AND
     * why nothing was done about it, in one line.</p>
     */
    static final String UNADMITTED =
            " (this replay was not admitted, so it states no topology)";

    /**
     * One pair against the skeleton: grow it, fill it, or contradict it.
     *
     * <p>The decision is per SLOT.  {@code byInteraction} answers it for the
     * pair itself, and the consumer-keyed map answers the R-I6 question that
     * a slot id cannot: whether a REPLAY has paired a WIRE consumer endpoint
     * with a producer other than the one the CATALOG holds it against.  That
     * is a cross-session statement about a message, and only that is a
     * replacement (R-I6; R-I7/R-I7.1 make a state pairing a path fact, and
     * the arms of one family are exactly the writers different sessions
     * delivered from).</p>
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
                         Endpoint consumer, String sessionId,
                         boolean authority, int wave,
                         List<Slot> opened, List<GapRow> gaps) {
        Slot slot = new Slot(kind, producer, consumer, sessionId, wave);
        String interaction = slot.interactionId();
        if (byInteraction.containsKey(interaction)) return Outcome.FILLED;
        // A STATE pairing is never a contradiction: every (writer, reader)
        // pair any session states is one more arm of that reader's family.
        Slot contradicted = replaced(kind, producer, consumer, sessionId);
        if (contradicted != null) {
            gaps.add(GapRow.of(sessionId, GapKind.TOPOLOGY_DIVERGENCE,
                    authority ? GapClass.BLOCKING : GapClass.DIAGNOSTIC,
                    consumer.toString(),
                    "the catalog pairs this consumer with producer "
                            + "endpoint " + contradicted.producer.id()
                            + ", opened by " + contradicted.openedBySession
                            + ", and this replay pairs it with "
                            + producer.id()
                            + ": a replacement, not growth"
                            + (authority ? "" : UNADMITTED)));
            return authority ? Outcome.REPLACED : Outcome.REPORTED;
        }
        // AND IT OPENS NOTHING EITHER.  A pairing the skeleton does not
        // hold would GROW it, and growth is a statement about the world
        // this epoch runs; a replay that did not run the world it was asked
        // for states that no more than it states a contradiction.
        if (!authority) {
            gaps.add(GapRow.of(sessionId, GapKind.TOPOLOGY_DIVERGENCE,
                    GapClass.DIAGNOSTIC, consumer.toString(),
                    "this replay pairs this consumer with producer endpoint "
                            + producer.id() + ", which this epoch's skeleton "
                            + "does not hold, and no slot is opened for it"
                            + UNADMITTED));
            return Outcome.REPORTED;
        }
        Slot held = kind == InteractionKind.WIRE
                ? slotOfConsumer.get(consumer.id()) : null;
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
        // The regions the RECORDING reached: a seed session replays it, so
        // an unretained region it ran is one the plan saw and chose not to
        // retain.  Reaching it again is not growth -- the export inside it
        // simply names the occurrence it ran in (Identity.currentOccurrence,
        // the one producer door) -- and only a region no seed reached is the
        // SS8 case 2 an epoch has to be re-cut for.
        Set<String> recorded = new LinkedHashSet<String>();
        for (SessionReader session : corpus.sessions()) {
            if (session.manifest() == null || session.manifest().role()
                    != edu.uva.liftlab.graphchecker.contract.SessionManifest
                            .Role.SEED) {
                continue;
            }
            for (ActivationRow activation : session.activations()) {
                if (!activation.instrumented()) {
                    recorded.add(activation.occurrence().regionId());
                }
            }
        }
        for (SessionReader session : authoritiesFirst(corpus)) {
            // The same rule: a replay that was not admitted states no
            // topology, so the region it reached is reported and the
            // retained set is not held to it.
            boolean authority = session.admitted();
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
                if (recorded.contains(occurrence.regionId())) {
                    gaps.add(GapRow.of(session.sessionId(),
                            GapKind.TOPOLOGY_DIVERGENCE, GapClass.DIAGNOSTIC,
                            occurrence.render(),
                            "reached and not retained, as in the recording: "
                                    + occurrence.regionId() + " ran in the "
                                    + "seed too, and the plan did not retain "
                                    + "it"));
                    continue;
                }
                gaps.add(GapRow.of(session.sessionId(),
                        GapKind.TOPOLOGY_DIVERGENCE,
                        authority ? GapClass.BLOCKING : GapClass.DIAGNOSTIC,
                        occurrence.render(),
                        "retained set must grow: " + occurrence.regionId()
                                + (authority ? "" : UNADMITTED)));
                divergence |= authority;
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
     *
     * <p>So the rule is per code point: a code point the closure holds is
     * REPLACED in a replay that ran it only under contexts the closure does
     * not hold there.  The closure may hold several members at one code
     * point, and a member that ran is never a replacement of one that did
     * not.</p>
     */
    private static boolean contextChanged(Corpus corpus, Set<String> closure,
                                          List<GapRow> gaps) {
        // EVERY member at a code point, not the last one filed: the closure
        // may hold two occurrences of one code point -- hdfs-17897's dn0
        // serves the client's handshake and the checksum leader's own at one
        // SASL callback, both members -- and a map to one member read a
        // replay that ran the other as a REPLACEMENT of the one it kept.
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
            // The same rule again: what this replay ran at a code point the
            // closure holds is a statement about the epoch's topology, and
            // a replay that was not admitted makes none.
            boolean authority = session.admitted();
            Set<String> ran = new LinkedHashSet<String>();
            for (ActivationRow activation : session.activations()) {
                ran.add(activation.occurrence().id());
            }
            for (ActivationRow activation : session.activations()) {
                OccurrenceAddress occurrence = activation.occurrence();
                List<OccurrenceAddress> members =
                        byCodePoint.get(codePoint(occurrence));
                if (members == null) continue;
                // A closure member is never the replacement of another: what
                // stands there is itself held.
                if (closure.contains(occurrence.id())) continue;
                // Some member ran here too: two occurrences of one code
                // point, which is what a second request IS.
                boolean memberRan = false;
                for (OccurrenceAddress member : members) {
                    if (ran.contains(member.id())) memberRan = true;
                }
                if (memberRan) continue;
                StringBuilder held = new StringBuilder();
                for (OccurrenceAddress member : members) {
                    if (held.length() > 0) held.append(", ");
                    held.append(member.context().render());
                }
                gaps.add(GapRow.of(session.sessionId(),
                        GapKind.TOPOLOGY_DIVERGENCE,
                        authority ? GapClass.BLOCKING : GapClass.DIAGNOSTIC,
                        occurrence.render(),
                        "the closure holds " + held
                                + " at this code point, and this replay ran "
                                + "it only under "
                                + occurrence.context().render()
                                + (authority ? "" : UNADMITTED)));
                replaced |= authority;
            }
        }
        return replaced;
    }

    /**
     * The corpus's sessions, the ones that state a topology first.
     *
     * <p>{@link #unretained} publishes ONE row per region, so the class of
     * that row has to be the strongest statement any session makes about
     * it: an admitted replay that reached an unretained region is a
     * BLOCKING fact whichever session the iteration met first.</p>
     */
    private static List<SessionReader> authoritiesFirst(Corpus corpus) {
        List<SessionReader> ordered = new ArrayList<SessionReader>();
        for (SessionReader session : corpus.sessions()) {
            if (session.admitted()) ordered.add(session);
        }
        for (SessionReader session : corpus.sessions()) {
            if (!session.admitted()) ordered.add(session);
        }
        return ordered;
    }

    /** The same code point in the same control context. */
    private static String codePoint(OccurrenceAddress occurrence) {
        return occurrence.node().render() + "/" + occurrence.regionId() + "/"
                + occurrence.index().hash();
    }
}
