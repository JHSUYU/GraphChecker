package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RowOrder;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.RowPool;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.smt.JsonFields;


import java.io.IOException;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.NoSuchFileException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

public final class SlotTable {
    public static final String FILE = "slots.jsonl.gz";
    static final String OPENED = "SLOT";
    static final String DROPPED = "SLOT_DROPPED";
    private static final String ROUNDS = "obligations-";

    public static final class Slot {
        public final InteractionKind kind;
        public final Endpoint producer;
        public final Endpoint consumer;
        public final String openedBySession;
        public final int openedAtRound;
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

    private final Map<Key, Slot> byInteraction =
            new LinkedHashMap<Key, Slot>();
    private final Set<Key> answeredSlots = new HashSet<Key>();
    private final Map<String, Slot> slotOfConsumer =
            new HashMap<String, Slot>();
    private final Map<String, Slot> ownChainOf = new HashMap<String, Slot>();
    private final List<Change> changes = new ArrayList<Change>();

    private static final class Change {
        final Slot slot;
        final String kind;

        Change(Slot slot, String kind) {
            this.slot = slot;
            this.kind = kind;
        }
    }
    private boolean stated;

    SlotTable() {
    }

    public static SlotTable read(Path iteration) throws IOException {
        return read(iteration, Integer.MAX_VALUE);
    }

    public static SlotTable read(Path iteration, int round)
            throws IOException {
        SlotTable table = new SlotTable();
        if (iteration == null) return table;
        RowPool pool = new RowPool();
        for (Path file : files(iteration, round)) {
            if (!Files.isRegularFile(file)) continue;
            table.stated = true;
            RowCodec.readEach(file, pool, row -> new ChangeRead(
                    ExploreCodec.readSlot(row, pool),
                    JsonFields.optionalString(row, "kind")), change -> {
                if (DROPPED.equals(change.kind)) {
                    table.byInteraction.remove(change.key);
                } else {
                    table.byInteraction.put(change.key, change.slot);
                }
            });
        }
        return table;
    }

    private static final class ChangeRead {
        final Slot slot;
        final Key key;
        final String kind;

        ChangeRead(Slot slot, String kind) {
            this.slot = slot;
            this.key = key(slot);
            this.kind = kind;
        }
    }

    public static List<Path> files(Path iteration) throws IOException {
        return files(iteration, Integer.MAX_VALUE);
    }

    private static List<Path> files(Path iteration, int round)
            throws IOException {
        List<Path> files = new ArrayList<Path>();
        files.add(iteration.resolve(FILE));
        Map<Integer, Path> rounds = new TreeMap<Integer, Path>();
        try (DirectoryStream<Path> dirs =
                     Files.newDirectoryStream(iteration, ROUNDS + "*")) {
            for (Path dir : dirs) {
                String number = dir.getFileName().toString()
                        .substring(ROUNDS.length());
                if (!number.matches("[0-9]+")) continue;
                int at = Integer.parseInt(number);
                if (at < round) rounds.put(at, dir.resolve(FILE));
            }
        } catch (NoSuchFileException none) {
            return Collections.<Path>emptyList();
        }
        files.addAll(rounds.values());
        return files;
    }

    public boolean stated() {
        return stated;
    }

    public Set<String> wireConsumers() {
        Set<String> consumers = new HashSet<String>();
        for (Slot slot : byInteraction.values()) {
            if (slot.kind == InteractionKind.WIRE) {
                consumers.add(slot.consumer.id());
            }
        }
        return consumers;
    }

    public void write(Path roundDir) throws IOException {
        RowCodec.writeAll(roundDir.resolve(FILE), changes,
                change -> ExploreCodec.writeSlot(change.slot, change.kind));
        changes.clear();
    }

    public int size() {
        return byInteraction.size();
    }

    private static Key key(Slot slot) {
        return key(slot.kind, slot.producer, slot.consumer, slot.world);
    }

    private static Key key(InteractionKind kind, Endpoint producer,
                           Endpoint consumer, String world) {
        return new Key(kind, producer.id(), consumer.id(), world);
    }

    private static final class Key {
        private final InteractionKind kind;
        private final String producer;
        private final String consumer;
        private final String world;

        Key(InteractionKind kind, String producer, String consumer,
            String world) {
            this.kind = kind;
            this.producer = producer;
            this.consumer = consumer;
            this.world = world;
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) return true;
            if (!(other instanceof Key)) return false;
            Key key = (Key) other;
            return kind == key.kind && producer.equals(key.producer)
                    && consumer.equals(key.consumer)
                    && world.equals(key.world);
        }

        @Override
        public int hashCode() {
            return ((kind.hashCode() * 31 + producer.hashCode()) * 31
                    + consumer.hashCode()) * 31 + world.hashCode();
        }
    }

    private void open(Key key, Slot slot, boolean answered) {
        byInteraction.put(key, slot);
        changes.add(new Change(slot, OPENED));
        index(key, slot, answered);
    }

    private void index(Key key, Slot slot, boolean answered) {
        if (answered) {
            answeredSlots.add(key);
        } else {
            answeredSlots.remove(key);
        }
        if (slot.kind != InteractionKind.WIRE) return;
        if (answered) {
            ownChainOf.put(slot.consumer.id() + "|" + slot.world + "|"
                    + slot.openedBySession, slot);
        } else {
            slotOfConsumer.put(slot.consumer.id() + "|" + slot.world, slot);
        }
    }

    private Map<String, Set<String>> standing(Corpus corpus) {
        Map<String, Set<String>> answeredIn =
                new HashMap<String, Set<String>>();
        for (SessionReader session : corpus.sessions()) {
            answeredIn.put(session.sessionId(), session.answered());
        }
        answeredSlots.clear();
        slotOfConsumer.clear();
        ownChainOf.clear();
        for (Iterator<Map.Entry<Key, Slot>> held = byInteraction
                .entrySet().iterator(); held.hasNext(); ) {
            Map.Entry<Key, Slot> entry = held.next();
            Slot slot = entry.getValue();
            Set<String> answered = answeredIn.get(slot.openedBySession);
            if (answered == null) {
                held.remove();
                changes.add(new Change(slot, DROPPED));
                continue;
            }
            index(entry.getKey(), slot, slot.kind == InteractionKind.WIRE
                    && answered.contains(slot.consumer.occurrence().render()));
        }
        return answeredIn;
    }

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

    private static boolean contradictsOrder(ReadRow read,
                                            WriteRow observed) {
        return RowOrder.before(read, observed);
    }

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
                Slot held = replaced(key(InteractionKind.WIRE,
                        attach.producer(), attach.endpoint(), world),
                        InteractionKind.WIRE, attach.producer(),
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

    private Slot replaced(Key key, InteractionKind kind, Endpoint producer,
                          Endpoint consumer, String sessionId, String world) {
        if (kind != InteractionKind.WIRE) return null;
        if (holds(key, false)) return null;
        Slot held = slotOfConsumer.get(consumer.id() + "|" + world);
        if (held == null || held.producer.id().equals(producer.id())) {
            return null;
        }
        return held.openedBySession.equals(sessionId) ? null : held;
    }

    private boolean holds(Key key, boolean answered) {
        return byInteraction.containsKey(key)
                && (answered || !answeredSlots.contains(key));
    }

    private enum Outcome { OPENED, FILLED, REPLACED, AMBIGUOUS, REPORTED }

    static final String UNADMITTED =
            " (this replay was not admitted, so it states no topology)";

    private Outcome take(InteractionKind kind, Endpoint producer,
                         Endpoint consumer, String sessionId, String world,
                         boolean authority, boolean answered, int round,
                         List<Slot> opened, List<GapRow> gaps) {
        Slot slot = new Slot(kind, producer, consumer, sessionId, round, world);
        Key key = key(slot);
        if (holds(key, answered)) return Outcome.FILLED;
        Slot contradicted = answered ? null
                : replaced(key, kind, producer, consumer, sessionId, world);
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
        open(key, slot, answered);
        opened.add(slot);
        return Outcome.OPENED;
    }

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
        Map<CausalContext, List<String>> shapes =
                new HashMap<CausalContext, List<String>>();
        Map<String, Set<String>> running = new HashMap<String, Set<String>>();
        boolean replaced = false;
        for (SessionReader session : corpus.sessions()) {
            boolean authority = session.admitted();
            String world = ObligationFactory.worldDigest(
                    corpus.world(session.sessionId()));
            Map<String, List<OccurrenceAddress>> ran =
                    new HashMap<String, List<OccurrenceAddress>>();
            for (ActivationRow activation : session.activations()) {
                String at = codePoint(activation.occurrence());
                if (byCodePoint.containsKey(at)) {
                    ran.computeIfAbsent(at,
                            key -> new ArrayList<OccurrenceAddress>())
                            .add(activation.occurrence());
                }
            }
            Map<String, Boolean> memberRan = new HashMap<String, Boolean>();
            Set<String> moved = new HashSet<String>();
            for (ActivationRow activation : session.activations()) {
                OccurrenceAddress occurrence = activation.occurrence();
                String at = codePoint(occurrence);
                List<OccurrenceAddress> members = byCodePoint.get(at);
                if (members == null || closure.contains(occurrence.id())
                        || memberRan.computeIfAbsent(at, point -> ranMember(
                                corpus, members, ran.get(point), shapes))) {
                    continue;
                }
                OccurrenceAddress[] elsewhere = movedTo(corpus, members,
                        session, shapes);
                if (elsewhere != null) {
                    if (moved.add(at)) {
                        gaps.add(GapRow.of(session.sessionId(),
                                GapKind.ADDRESS_UNSTABLE, GapClass.DIAGNOSTIC,
                                elsewhere[0].render(), "this replay ran the "
                                        + "closure's member under its own "
                                        + "context on "
                                        + elsewhere[1].node().render()
                                        + ": the world placed it there, and "
                                        + "what ran at its code point here is"
                                        + " other work"));
                    }
                    continue;
                }
                boolean sameWorld = false;
                StringBuilder held = new StringBuilder();
                for (OccurrenceAddress member : members) {
                    sameWorld |= running.computeIfAbsent(member.id(),
                            id -> worldsRunning(corpus, member))
                            .contains(world);
                    if (held.length() > 0) held.append(", ");
                    held.append(member.context().render());
                }
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

    private static OccurrenceAddress[] movedTo(Corpus corpus,
                                               List<OccurrenceAddress> members,
                                               SessionReader session,
                                               Map<CausalContext,
                                                       List<String>> shapes) {
        for (ActivationRow activation : session.activations()) {
            OccurrenceAddress ran = activation.occurrence();
            if (ran.context().isLost()) continue;
            for (OccurrenceAddress member : members) {
                if (ran.regionId().equals(member.regionId())
                        && ran.index().hash().equals(member.index().hash())
                        && !ran.node().equals(member.node())
                        && ContextShape.same(shapes.computeIfAbsent(
                                ran.context(), corpus::contextShape),
                        shapes.computeIfAbsent(member.context(),
                                corpus::contextShape))) {
                    return new OccurrenceAddress[] {member, ran};
                }
            }
        }
        return null;
    }

    private static boolean ranMember(Corpus corpus,
                                     List<OccurrenceAddress> members,
                                     List<OccurrenceAddress> ran,
                                     Map<CausalContext, List<String>> shapes) {
        for (OccurrenceAddress occurrence : ran) {
            for (OccurrenceAddress member : members) {
                if (ContextShape.sameQuestion(occurrence, member,
                        context -> shapes.computeIfAbsent(context,
                                corpus::contextShape))) {
                    return true;
                }
            }
        }
        return false;
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

    private static String codePoint(OccurrenceAddress occurrence) {
        return occurrence.node().render() + "/" + occurrence.regionId() + "/"
                + occurrence.index().hash();
    }
}
