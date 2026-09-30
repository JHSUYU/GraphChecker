package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Term;

import edu.uva.liftlab.graphchecker.contract.Arm;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.Family;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.explore.Corpus;
import edu.uva.liftlab.graphchecker.explore.SlotTable;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.smtLiteral;

/**
 * The families of one composition: a slot's alternative deliveries in SMT
 * ({@code Arms} decides what an arm IS).  WIRE families via {@link
 * #closeFamilies}, STATE families via {@link #stateFamilies}.  It holds the
 * composition's own collections, not copies, and reaches {@link Composer}
 * for gaps, the epoch's slot table and the path routines an arm is closed
 * by (closure, stated reads, state joins, prefixes).
 */
final class ComposedFamilies {

    private final Composer composer;
    private final Corpus corpus;
    private final Arms arms;
    private final SmtLowering lowering;
    private final Map<String, Family> families;
    private final Map<String, Set<String>> unattestedRoots;
    private final Set<String> replacing;
    private final List<GapRow> gaps;
    /** Interactions already remarked on, so one row says it once. */
    private final Set<String> slotNamed = new LinkedHashSet<String>();
    /** Attaches already named as unpaired; one row per attach, not path. */
    private final Set<String> unpairedNamed = new LinkedHashSet<String>();
    /** Locations already named as aliasing, so one row says it once. */
    private final Set<String> aliasingNamed = new LinkedHashSet<String>();

    ComposedFamilies(Composer composer, Corpus corpus, Arms arms,
                     SmtLowering lowering, Map<String, Family> families,
                     Map<String, Set<String>> unattestedRoots,
                     Set<String> replacing, List<GapRow> gaps) {
        this.composer = composer;
        this.corpus = corpus;
        this.arms = arms;
        this.lowering = lowering;
        this.families = families;
        this.unattestedRoots = unattestedRoots;
        this.replacing = replacing;
        this.gaps = gaps;
    }

    /**
     * Which delivery a family's selector stands for: the manifest's answer
     * to "which arm did the witness take".
     */
    public static final class ArmChoice {
        private final String family;
        private final String groupId;
        private final List<String> attachEndpointIds;
        private final List<String> sessionIds;
        private final String producerPathId;
        private final List<String> interactionIds;
        private final List<String> expressionRefs;
        private final boolean attested;

        private ArmChoice(String family, String groupId,
                          List<String> attachEndpointIds,
                          List<String> sessionIds, String producerPathId,
                          List<String> interactionIds,
                          List<String> expressionRefs, boolean attested) {
            this.family = family;
            this.groupId = groupId;
            this.attachEndpointIds = Collections.unmodifiableList(
                    attachEndpointIds);
            this.sessionIds = Collections.unmodifiableList(sessionIds);
            this.producerPathId = producerPathId;
            this.interactionIds = Collections.unmodifiableList(
                    interactionIds);
            this.expressionRefs = Collections.unmodifiableList(
                    expressionRefs);
            this.attested = attested;
        }

        static ArmChoice of(String family, String groupId,
                            List<String> attachEndpointIds, String session,
                            List<Arms.Arm> arms) {
            List<String> slots = new ArrayList<String>();
            List<String> refs = new ArrayList<String>();
            String path = "";
            boolean attested = true;
            for (Arms.Arm arm : arms) {
                if (!slots.contains(arm.slotId())) slots.add(arm.slotId());
                if (!refs.contains(arm.expressionRef())) {
                    refs.add(arm.expressionRef());
                }
                if (path.isEmpty()) path = arm.producerPathId();
                attested = attested && arm.attested();
            }
            return new ArmChoice(family, groupId, attachEndpointIds,
                    new ArrayList<String>(Collections.singletonList(
                            session)), path, slots, refs, attested);
        }

        /** The same arm, stated by one more run. */
        ArmChoice alsoBy(String session) {
            List<String> sessions = new ArrayList<String>(sessionIds);
            sessions.add(session);
            return new ArmChoice(family, groupId, attachEndpointIds,
                    sessions, producerPathId, interactionIds,
                    expressionRefs, attested);
        }

        /** The named assertion this arm-set is one case of. */
        public String family() {
            return family;
        }

        /**
         * What this selector stands for as produced by one run: the message
         * (spelled by its leaves) or, for a state family, a writer occurrence.
         */
        public String groupId() {
            return groupId;
        }

        /** The attach endpoints one message was received at. */
        public List<String> attachEndpointIds() {
            return attachEndpointIds;
        }

        /** The run that made it: the first of {@link #sessionIds}. */
        public String sessionId() {
            return sessionIds.get(0);
        }

        /** Every run whose producer path is this arm, letter for letter. */
        public List<String> sessionIds() {
            return sessionIds;
        }

        /** The producer path, or "" when no path condition attests it. */
        public String producerPathId() {
            return producerPathId;
        }

        /** Every interaction this one selector binds. */
        public List<String> interactionIds() {
            return interactionIds;
        }

        /** The expression delivered at each of them. */
        public List<String> expressionRefs() {
            return expressionRefs;
        }

        public boolean attested() {
            return attested;
        }
    }

    /** Arm selector -> the delivery it stands for. */
    private final Map<String, ArmChoice> armChoices =
            new LinkedHashMap<String, ArmChoice>();

    /** Every arm selector this composition declared, in the order made. */
    Map<String, ArmChoice> armChoices() {
        return Collections.unmodifiableMap(armChoices);
    }

    /**
     * ONE SELECTOR PER (MESSAGE, SESSION), exactly one eligible
     * session per message.  The unit is the MESSAGE (correlation id), not
     * the producer occurrence: per-leaf choices let a witness mix halves of
     * two runs' responses.  Wire arrivals are bound HERE only (PIPELINE §8);
     * a message no session could send is refused by name.
     *
     * @return whether every message this path binds has an eligible
     *         session; if not, the path leaves the disjunction
     */
    boolean closeFamilies(int ordinal, String selector, String owner,
                          Set<String> reached,
                          List<AttachRow> bound, List<String> stated,
                          List<GapRow> refusals) {
        return closeMessages(ordinal, selector, owner, bound, reached,
                stated, refusals, new LinkedHashSet<String>(), 0);
    }

    /** How deep one delivery may be handed on before this refuses. */
    private static final int NESTING_LIMIT = 16;

    /**
     * The message groups of one set of attaches, under one guard: the path
     * selector for its own attaches, or a family guard for the attaches a
     * delivery was itself handed (item (iv) below) -- the same rule at every
     * depth.
     * A message closed at an outer level is not closed again.
     */
    private boolean closeMessages(int ordinal, String guard, String owner,
                                  List<AttachRow> attaches,
                                  Set<String> reached, List<String> stated,
                                  List<GapRow> refusals,
                                  Set<String> closedGroups, int depth) {
        if (depth > NESTING_LIMIT) {
            composer.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, guard,
                    "a delivery this path rests on was handed on more than "
                            + NESTING_LIMIT + " times, so the corpus states "
                            + "no end to what it rests on");
            return false;
        }
        // (1) Messages by correlation id; an attach with none is its own.
        Map<String, List<AttachRow>> byMessage =
                new LinkedHashMap<String, List<AttachRow>>();
        Set<String> seen = new LinkedHashSet<String>();
        for (AttachRow attach : attaches) {
            if (attach.interaction() == null) continue;
            if (!seen.add(attach.endpoint().id())) continue;
            String correlation = attach.correlationId();
            add(byMessage, correlation == null || correlation.isEmpty()
                    ? "@" + attach.endpoint().id() : correlation, attach);
        }
        for (Map.Entry<String, List<AttachRow>> message
                : byMessage.entrySet()) {
            List<AttachRow> leaves = message.getValue();
            if (!closedGroups.add(groupId(leaves))) continue;
            // (2) Each leaf's arms, one hop deep, and who attests them.
            Map<String, Interaction> slotOf =
                    new LinkedHashMap<String, Interaction>();
            Map<String, String> symbolOf =
                    new LinkedHashMap<String, String>();
            Map<String, List<Arms.Arm>> bySession =
                    new LinkedHashMap<String, List<Arms.Arm>>();
            Map<String, Set<String>> attestedAt =
                    new LinkedHashMap<String, Set<String>>();
            for (AttachRow attach : leaves) {
                Interaction slot = attach.interaction();
                if (slotOf.containsKey(slot.id())) continue;
                slotOf.put(slot.id(), slot);
                symbolOf.put(slot.id(), attach.symbol());
                attestedAt.put(slot.id(), new LinkedHashSet<String>());
                for (Arms.Arm arm : arms.armsAt(slot, attach.symbol())) {
                    if (replacing.contains(arm.sessionId())) continue;
                    if (arm.producer() == null) continue;
                    if (!arm.attested()) {
                        noteUnattested(arm, "that run is no option for this "
                                + "message, because the arm states what was "
                                + "delivered and not why");
                        continue;
                    }
                    add(bySession, arm.sessionId(), arm);
                    attestedAt.get(slot.id()).add(arm.sessionId());
                }
                fileRefusals();
            }
            // (3) and (4): eligibility, then one case split per message.
            List<String> eligible = eligibleSessions(message.getKey(),
                    slotOf.keySet(), attestedAt, refusals);
            if (eligible == null) return false;
            if (!messageFamily(ordinal, guard, owner, message.getKey(),
                    leaves, slotOf, symbolOf, eligible, attestedAt,
                    bySession, reached, stated, refusals, closedGroups,
                    depth)) {
                return false;
            }
        }
        return true;
    }

    /** One message's identity: the leaves it was received at. */
    private static String groupId(List<AttachRow> leaves) {
        List<String> ids = endpointIds(leaves);
        Collections.sort(ids);
        return String.join("|", ids);
    }

    /**
     * The sessions that could have SENT this message (PIPELINE §8) -- those
     * with an attested arm at EVERY interaction it covers.  A per-leaf check would
     * accept a run that sent only part of the response.
     *
     * @return the eligible sessions, or null (refused by name) when none is
     */
    private List<String> eligibleSessions(
            String message, Set<String> slots,
            Map<String, Set<String>> attestedAt, List<GapRow> refusals) {
        Set<String> eligible = null;
        for (String slotId : slots) {
            Set<String> sessions = attestedAt.get(slotId);
            if (sessions == null) {
                sessions = Collections.<String>emptySet();
            }
            if (eligible == null) {
                eligible = new LinkedHashSet<String>(sessions);
            } else {
                eligible.retainAll(sessions);
            }
            if (eligible.isEmpty()) {
                refusals.add(GapRow.of(corpus.seedSessionId(),
                        GapKind.UNPRODUCIBLE_ANSWER, GapClass.DIAGNOSTIC,
                        message, "no session of this corpus states an "
                                + "attested delivery at every leaf of this "
                                + "message: the first it cannot answer is "
                                + slotId + ", and a witness that took two "
                                + "runs' halves of one message would rest "
                                + "on a delivery no run made"));
                return null;
            }
        }
        return eligible == null ? new ArrayList<String>()
                : new ArrayList<String>(eligible);
    }

    /**
     * One message as a finite case split over the runs that could have sent
     * it: {@code sel_{M,S} => (guard_S /\ closure_{M,S} /\ v_H_k = e_{k,S})}
     * with exactly-one over the eligible sessions, so z3 decides by cases
     * and the model names which RUN's response the witness rests on.
     */
    private boolean messageFamily(
            int ordinal, String guard, String owner, String message,
            List<AttachRow> leaves, Map<String, Interaction> slotOf,
            Map<String, String> symbolOf, List<String> eligible,
            Map<String, Set<String>> attestedAt,
            Map<String, List<Arms.Arm>> bySession, Set<String> reached,
            List<String> stated, List<GapRow> refusals,
            Set<String> closedGroups, int depth) {
        String group = groupId(leaves);
        List<String> senders = compatible(owner, eligible);
        if (senders.isEmpty()) {
            refusals.add(GapRow.of(owner, GapKind.UNPRODUCIBLE_ANSWER,
                    GapClass.DIAGNOSTIC, message, "none of the "
                            + eligible.size() + " session(s) eligible to "
                            + "have sent this message ran in a world "
                            + "compatible with this path's, so no "
                            + "delivery this path could have received "
                            + "binds what it read"));
            return false;
        }
        String name = "message_family__" + ordinal + "__"
                + ArtifactIO.digest(group, 12);
        List<String> selectors = new ArrayList<String>();
        List<String> cases = new ArrayList<String>();
        // Arm body -> selector: one producer path is ONE arm however many
        // runs recorded it; copies are a symmetry the solver must break.
        Map<String, String> selectorOf = new LinkedHashMap<String, String>();
        List<String> representatives = new ArrayList<String>();
        for (String session : senders) {
            List<Arms.Arm> held = oneArmPerLeaf(bySession.get(session),
                    message, session);
            if (held == null || held.isEmpty()) continue;
            String selector = "message_arm__" + ordinal + "__"
                    + ArtifactIO.digest(group + "|" + session, 12);
            // Declared BEFORE the body: nested families are asserted under
            // this name even if the arm-set is then refused, and an
            // undeclared name makes z3 answer with an error.
            lowering.declare(selector, VmTermLowering.Sort.BOOL);
            List<String> nested = new ArrayList<String>();
            String body = producerBody(ordinal, guard, message, session,
                    bindings(held), reached, nested, closedGroups, depth);
            if (body == null) continue;
            stated.addAll(nested);
            String same = selectorOf.get(body);
            if (same != null) {
                armChoices.put(same, armChoices.get(same).alsoBy(session));
                continue;
            }
            selectorOf.put(body, selector);
            representatives.add(session);
            selectors.add(selector);
            cases.add("(=> " + selector + " " + body + ")");
            armChoices.put(selector, ArmChoice.of(name, group,
                    endpointIds(leaves), session, held));
        }
        if (selectors.isEmpty()) {
            refusals.add(GapRow.of(corpus.seedSessionId(),
                    GapKind.UNPRODUCIBLE_ANSWER, GapClass.DIAGNOSTIC,
                    message, "every session whose world is compatible "
                            + "with this path's (" + senders.size()
                            + " of the " + eligible.size() + " eligible) "
                            + "rests on a value the recording does not "
                            + "state, so nothing binds what this path read "
                            + "from it"));
            return false;
        }
        for (Map.Entry<String, Interaction> slot : slotOf.entrySet()) {
            reached.add(slot.getKey());
            slotOpened(slot.getKey(), slot.getValue());
            List<Arm> rows = new ArrayList<Arm>();
            for (String session : representatives) {
                List<Arms.Arm> held = bySession.get(session);
                if (held == null) continue;
                for (Arms.Arm arm : held) {
                    if (arm.slotId().equals(slot.getKey())) {
                        rows.add(row(arm));
                    }
                }
            }
            families.put(slot.getKey(), Family.of(slot.getKey(), rows));
        }
        cases.add(0, Arms.exactlyOne(selectors));
        String formula = VmTermLowering.and(cases);
        stated.add(formula);
        lowering.assertNamed(name, "(=> " + guard + " " + formula + ")");
        return true;
    }

    /**
     * The eligible sessions whose WORLD is compatible with this path's
     * (PIPELINE §8): one flip set contains the other.  Each is one arm, so
     * the value read is an {@code ite} over the deliveries its world admits,
     * and a producer flip becomes an alternative inside the path.  The own
     * session is the case where the two worlds are equal.
     */
    private List<String> compatible(String owner, List<String> eligible) {
        Set<String> path = flips(owner);
        List<String> arms = new ArrayList<String>();
        for (String session : eligible) {
            Set<String> producer = flips(session);
            if (path.containsAll(producer) || producer.containsAll(path)) {
                arms.add(session);
            }
        }
        return arms;
    }

    /** The decisions one session was held to, own and inherited. */
    private Set<String> flips(String session) {
        Set<String> held = new LinkedHashSet<String>();
        for (Corpus.Flip flip : corpus.world(session).flips) {
            held.add(flip.focusedOccurrenceId + "|" + flip.siteId + "#"
                    + flip.ordinal + "=" + flip.outcome);
        }
        return held;
    }

    /** The leaves one message was received at, in the rows' own order. */
    private static List<String> endpointIds(List<AttachRow> leaves) {
        List<String> ids = new ArrayList<String>();
        for (AttachRow attach : leaves) {
            if (!ids.contains(attach.endpoint().id())) {
                ids.add(attach.endpoint().id());
            }
        }
        return ids;
    }

    /**
     * ONE delivery per leaf.  The selector binds every leaf at once, so two
     * different arms of one session at one leaf would force {@code e1 = e2};
     * identical rows are deduplicated, different ones refuse the whole
     * {@code (message, S)} arm-set by name.
     */
    private List<Arms.Arm> oneArmPerLeaf(List<Arms.Arm> group,
                                         String message, String session) {
        if (group == null) return null;
        Map<String, Arms.Arm> byLeaf = new LinkedHashMap<String, Arms.Arm>();
        for (Arms.Arm arm : group) {
            String leaf = arm.slotId() + "|" + arm.symbol();
            Arms.Arm held = byLeaf.get(leaf);
            if (held == null) {
                byLeaf.put(leaf, arm);
                continue;
            }
            if (held.expressionRef().equals(arm.expressionRef())) continue;
            composer.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    message, "session " + session + " states two different "
                            + "deliveries at " + arm.slotId() + " ("
                            + held.expressionRef() + " and "
                            + arm.expressionRef() + "), so which one that "
                            + "run made is not in this corpus");
            return null;
        }
        return new ArrayList<Arms.Arm>(byLeaf.values());
    }

    /** One arm and the variables this path binds to it. */
    private static final class Out {
        private final Arms.Arm arm;
        private final List<String> symbols;

        private Out(Arms.Arm arm, List<String> symbols) {
            this.arm = arm;
            this.symbols = symbols;
        }
    }

    /** A wire arm binds the consumer's own variable and nothing else. */
    private static List<Out> bindings(List<Arms.Arm> group) {
        List<Out> outs = new ArrayList<Out>();
        for (Arms.Arm arm : group) {
            outs.add(new Out(arm, Collections.singletonList(arm.symbol())));
        }
        return outs;
    }

    /**
     * AN ARM IS CLOSED LIKE A PATH (PIPELINE §8), under {@code sel_{P,S}}
     * in S's scope: (i) P's decisions before the LAST delivery this path takes;
     * (ii) P's closure at that cutoff plus the versions the delivered
     * expressions read ({@link #expressionWrites}); (iii) the prefixes and
     * the joins this arm's text reaches, by the path's own routines; (iv)
     * P's own attaches as nested families.  Without (i)-(iii) an arm says
     * WHAT was delivered, not why.
     *
     * @return the arm-set's conjunction, or null when a value it rests on is
     *         not stated -- refusing this {@code (P, S)}, not the path
     */
    private String producerBody(int ordinal, String nestedGuard,
                                String subject,
                                String session,
                                List<Out> outs, Set<String> reachedSlots,
                                List<String> nestedStated,
                                Set<String> closedProducers, int depth) {
        List<GapRow> local = new ArrayList<GapRow>();
        SmtLowering.SessionJoin rows = corpus.join(session);
        lowering.begin(session, rows, corpus.expressions(session));
        List<String> conjuncts = new ArrayList<String>();
        boolean stated = true;
        // The bindings: what this run delivered at each out.
        Map<String, String> guards = new LinkedHashMap<String, String>();
        for (Out out : outs) {
            Term delivered = lower(session, out.arm.expressionRef(),
                    "arm:" + out.arm.slotId(), conjuncts);
            if (delivered == null) {
                stated = false;
                break;
            }
            for (String symbol : out.symbols) {
                if (symbol == null || symbol.isEmpty()) continue;
                lowering.declareStated(symbol, delivered.sort);
                conjuncts.add("(= " + symbol + " " + delivered.text + ")");
            }
            guards.putAll(out.arm.guard());
        }
        // The delivering replay's valuation of every varied root.
        for (Map.Entry<String, String> guard : guards.entrySet()) {
            String literal = smtLiteral(guard.getValue());
            if (literal.isEmpty()) continue;
            // The guard's root must be declared: an arm need not mention
            // it, and an undeclared constant makes z3 answer with an error.
            if (!lowering.declareStated(guard.getKey())) {
                composer.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        guard.getKey(), "an arm of " + subject
                                + " is guarded by a symbol no row of this "
                                + "corpus declares a sort for");
                continue;
            }
            conjuncts.add("(= " + guard.getKey() + " " + literal + ")");
        }
        List<String> nested = new ArrayList<String>();
        Map<String, String> joins = new LinkedHashMap<String, String>();
        if (stated) {
            // The closure of every producer occurrence of this group, each
            // from its OWN delivery cutoff, merged at the widest cutoff.
            Map<String, Long> reached = new LinkedHashMap<String, Long>();
            for (Map.Entry<String, List<Out>> each
                    : byProducer(outs).entrySet()) {
                List<Out> its = each.getValue();
                long cutoff = Long.MIN_VALUE;
                for (Out out : its) {
                    cutoff = Math.max(cutoff, out.arm.deliveredAt());
                }
                Map<String, Long> one = composer.closure(session,
                        its.get(0).arm.producer(), cutoff,
                        expressionWrites(session, its));
                for (Map.Entry<String, Long> at : one.entrySet()) {
                    Long was = reached.get(at.getKey());
                    if (was == null
                            || was.longValue() < at.getValue().longValue()) {
                        reached.put(at.getKey(), at.getValue());
                    }
                }
            }
            // What the delivered values rest on (Independence).
            List<String> delivered = new ArrayList<String>();
            for (Out out : outs) delivered.add(out.arm.expressionRef());
            Independence relevant = composer.independence(session,
                    delivered, reached,
                    composer.reachedConditions(session, reached));
            Set<String> answered = new LinkedHashSet<String>();
            composer.statedReads(session, reached.keySet(), relevant, rows,
                    local, joins, answered);
            composer.stateJoins(session, reached.keySet(), relevant, rows,
                    local, new ArrayList<ReadRow>(), joins, answered);
            conjuncts.addAll(composer.closureConditions(session, reached,
                    relevant, local));
            // Nested families go under this FAMILY's guard, not this
            // session's selector: sessions share the leaf's handoff symbol,
            // so a nested family under one selector leaves it unbound for
            // the others.
            stated = closeMessages(ordinal, nestedGuard, session,
                    nestedAttaches(session, outs), reachedSlots, nested,
                    local, closedProducers, depth + 1);
        }
        List<String> reachTexts = new ArrayList<String>(conjuncts);
        reachTexts.addAll(nested);
        conjuncts.addAll(composer.statedJoins(joins,
                Collections.<String>emptySet(), reachTexts,
                Collections.<String>emptyList()));
        List<String> refused = new ArrayList<String>(
                lowering.openRefusals());
        conjuncts.addAll(lowering.end());
        if (!stated || !local.isEmpty() || !refused.isEmpty()) {
            gaps.addAll(local);
            for (String refusal : refused) {
                composer.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        refusal, "the closure of " + subject
                                + " in session " + session + " rests on a "
                                + "value the recording does not state, so "
                                + "that run is not one of its options");
            }
            return null;
        }
        nestedStated.addAll(nested);
        return VmTermLowering.and(conjuncts);
    }

    /** One group's outs, by the occurrence each came out of. */
    private static Map<String, List<Out>> byProducer(List<Out> outs) {
        Map<String, List<Out>> held =
                new LinkedHashMap<String, List<Out>>();
        for (Out out : outs) {
            add(held, out.arm.producer().id(), out);
        }
        return held;
    }

    /**
     * The attaches one delivery was itself handed (item (iv) of an arm's
     * closure, above): the handoff
     * variables {@link Arms.Arm#nested} names, resolved in the delivering
     * session.
     */
    private List<AttachRow> nestedAttaches(String session, List<Out> outs) {
        List<AttachRow> attaches = new ArrayList<AttachRow>();
        Set<String> seen = new LinkedHashSet<String>();
        for (Out out : outs) {
            for (String symbol : out.arm.nested()) {
                if (!seen.add(symbol)) continue;
                AttachRow attach = corpus.attach(session, symbol);
                if (attach != null) attaches.add(attach);
            }
        }
        return attaches;
    }

    /**
     * The container VERSIONS a delivered expression reads: a projection
     * names the read, but the closure needs the write the producer had in
     * hand (latest version at or before the read).  Resolved only by
     * {@link Corpus#expressionStateReads}, the edge exploration grows by
     * too (PIPELINE §7.2), so arms and waves agree on what a delivery is made
     * of.
     */
    private List<WriteRow> expressionWrites(String session, List<Out> outs) {
        List<WriteRow> writes = new ArrayList<WriteRow>();
        Set<String> seen = new LinkedHashSet<String>();
        for (Out out : outs) {
            for (Corpus.StateRead read : corpus.expressionStateReads(
                    session, out.arm.expressionRef())) {
                if (!seen.add(read.locationKey() + "#"
                        + read.write().version())) {
                    continue;
                }
                writes.add(read.write());
            }
        }
        return writes;
    }

    /**
     * An arm whose producer ran concretely: what it delivered is stated and
     * why is not, so it is no option for that occurrence and no witness may
     * move a root inside it.
     */
    private void noteUnattested(Arms.Arm arm, String detail) {
        Set<String> held = unattestedRoots.computeIfAbsent(arm.slotId(),
                slot -> new LinkedHashSet<String>());
        SessionReader reader = corpus.session(arm.sessionId());
        JsonObject expression = reader == null ? null
                : reader.expressions().expression(arm.expressionRef());
        Set<String> symbols = new LinkedHashSet<String>();
        if (expression != null) Arms.symbolsIn(expression, symbols);
        for (Map.Entry<String, List<RootMintRow>> entry
                : corpus.roots().entrySet()) {
            RootMintRow row = corpus.anyRoot(entry.getKey());
            if (row == null || !row.declared()) continue;
            if (symbols.contains(row.symbol())) held.add(row.rootId());
        }
        composer.gap(GapKind.UNATTESTED_ARM, GapClass.DIAGNOSTIC,
                arm.slotId(), "the producer ran concretely in session "
                        + arm.sessionId() + ": " + detail);
    }

    /**
     * Files every arm {@link Arms} refused since the last drain
     * as this composition's gap, once.
     */
    private void fileRefusals() {
        for (String refusal : arms.drainRefusals()) {
            String[] named = refusal.split("\\|", -1);
            if (named.length != 3) continue;
            composer.gap(GapKind.UNATTESTED_ARM, GapClass.DIAGNOSTIC,
                    named[0], "an arm delivered by session " + named[1]
                            + " names root " + named[2] + " and that session"
                            + " states no RootMintRow for it, so the arm is"
                            + " refused");
        }
    }

    /** One arm as the manifest states it. */
    private static Arm row(Arms.Arm arm) {
        return Arm.of(arm.producerPathId().isEmpty() ? arm.sessionId()
                        : arm.producerPathId(), arm.producerPathId(),
                arm.expressionRef(), arm.guardRoots(), arm.attested());
    }

    /** Growth is not an event; the skeleton names what it has not opened. */
    private void slotOpened(String slotId, Interaction slot) {
        SlotTable slots = composer.slots();
        if (slots == null || !slots.stated()) return;
        if (slots.opened(slot.consumer().id())) return;
        if (!slotNamed.add(slotId)) return;
        composer.gap(GapKind.TOPOLOGY_DIVERGENCE, GapClass.DIAGNOSTIC, slotId,
                "this epoch's skeleton has opened no slot for this "
                        + "interaction yet; its arms are composed and the "
                        + "slot table will name it when exploration opens "
                        + "it");
    }

    private static <T> void add(Map<String, List<T>> index, String key,
                                T value) {
        index.computeIfAbsent(key, held -> new ArrayList<T>()).add(value);
    }

    /**
     * Names every recorded interaction this anchor does not reach -- a
     * diagnostic, never a refusal.
     */
    void outsideTheClosure(List<Composer.Disjunct> disjuncts) {
        Set<String> reached = new LinkedHashSet<String>();
        for (Composer.Disjunct disjunct : disjuncts) {
            reached.addAll(disjunct.interactionIds());
        }
        for (String interactionId : corpus.interactions().keySet()) {
            if (reached.contains(interactionId)) continue;
            if (!slotNamed.add(interactionId)) continue;
            composer.gap(GapKind.TOPOLOGY_DIVERGENCE, GapClass.DIAGNOSTIC,
                    interactionId, "no path admitted at this anchor reaches "
                            + "this interaction, so the composition records "
                            + "it and uses nothing from it");
        }
    }

    /**
     * An attach whose producer is not named: LINEAGE_LOST when a producer
     * endpoint exists but its address was lost, UNSTATED_VALUE when there is
     * no producer at all.
     */
    void unpaired(String session, AttachRow attach) {
        if (!unpairedNamed.add(session + "|" + attach.endpoint().id())) {
            return;
        }
        Endpoint producer = attach.producer();
        boolean degraded = producer != null
                && producer.occurrence() != null
                && producer.occurrence().lineageLost();
        gaps.add(GapRow.of(session,
                producer == null && !degraded ? GapKind.UNSTATED_VALUE
                        : GapKind.LINEAGE_LOST,
                GapClass.DIAGNOSTIC, attach.endpoint().toString(),
                "this attach names no producer endpoint, so the value it "
                        + "received joins no interaction and has no family; "
                        + "the arrival this session recorded is all the "
                        + "composition states about it"));
    }

    /**
     * THE STATE FAMILIES: one selector per writer, as a message family has
     * one per sender (PIPELINE §8), with the WRITER as P.  A writer
     * occurrence's writes move as a BLOCK, so one selector per writer binds
     * every joined read of every location it writes, its body stated once;
     * then exactly-one PER LOCATION over its writers (none for a single
     * writer).  Choosing a writer for one location and not another would
     * be half a block moved.  {@code recorded} receives each family's arm
     * the run took -- the observed writer's selector, or the pins' when no
     * region wrote a version read: the pairing a witness re-pairs if it
     * needs another.  A read's value is no such statement, since a joined
     * value moves with the valuation while its pairing stays.  Where no arm
     * is that pairing (the reads saw two writes, or the one they saw has no
     * arm) the run as it happened is no world of the formula, and a BLOCKING
     * gap says so: STATE_PAIRING_FLIPPED and the recording's own verdict pin
     * that pairing, and every other kind is named only once the pairing flip
     * is ruled out ({@link ClaimPolicy}).
     */
    Set<String> stateFamilies(Corpus.RecordedPath path,
                              int ordinal, String selector,
                              List<ReadRow> joined,
                              Map<String, String> pins,
                              Set<String> reached,
                              List<String> stated,
                              List<String> recorded) {
        String session = path.sessionId;
        Set<String> chosen = new LinkedHashSet<String>();
        // Reads grouped by location: every read of it takes the same arm.
        Map<String, List<ReadRow>> byLocation =
                new LinkedHashMap<String, List<ReadRow>>();
        for (ReadRow read : joined) {
            add(byLocation, SmtLowering.locationKey(read.location()), read);
        }
        // Each location's writers, and each writer's outs across locations.
        Map<String, List<String>> writersOf =
                new LinkedHashMap<String, List<String>>();
        Map<String, List<Out>> outsOfWriter =
                new LinkedHashMap<String, List<Out>>();
        // A location one of whose observed versions no row wrote: its reads'
        // joins and pins, the arm that is the run's own interleaving.
        Map<String, List<String>> observedPins =
                new LinkedHashMap<String, List<String>>();
        // Otherwise the writes its reads observed: version -> writer.
        Map<String, Map<Long, String>> observedWrites =
                new LinkedHashMap<String, Map<Long, String>>();
        for (Map.Entry<String, List<ReadRow>> entry
                : byLocation.entrySet()) {
            List<ReadRow> reads = entry.getValue();
            // Alternatives need an owner naming the storage
            // ({@link Arms#namedOwner}); a class owner aliases every
            // instance, so such a read keeps its own run's delivery.
            if (!Arms.namedOwner(reads.get(0).location())) {
                if (aliasingNamed.add(entry.getKey())) {
                    composer.gap(GapKind.DECLARATION_MISSING,
                            GapClass.DIAGNOSTIC,
                            entry.getKey(), "the owner on this location's "
                                    + "rows is a class and not the rid of "
                                    + "one object, so it names every "
                                    + "instance of that class at once: "
                                    + "this read is delivered as its own "
                                    + "run delivered it and gets no "
                                    + "alternative writers");
                }
                continue;
            }
            List<String> symbols = new ArrayList<String>();
            for (ReadRow read : reads) symbols.add(read.symbol());
            List<Arms.Arm> found = new ArrayList<Arms.Arm>();
            for (Arms.Arm arm : arms.stateArms(reads.get(0).endpoint(),
                    session, entry.getKey(),
                    reads.get(0).observedVersion())) {
                if (replacing.contains(arm.sessionId())) continue;
                if (arm.producer() == null) continue;
                // The OBSERVED writer is stated even if unattested.
                if (!arm.attested()) {
                    noteUnattested(arm, "the arm states what it wrote and "
                            + "not why, so no witness may move a root "
                            + "inside it");
                }
                // Recorded even without a case split: the unattested-arm
                // gate reads this set.
                reached.add(arm.slotId());
                families.put(arm.slotId(), Family.of(arm.slotId(),
                        Collections.singletonList(row(arm))));
                found.add(arm);
            }
            fileRefusals();
            // What EVERY read of it observed, not the first's.  A version
            // whose writer ran outside every region is stated by no arm: the
            // pins are, as one more arm holding each read to its own join or
            // pin, the run as it happened.
            boolean outside = false;
            Map<Long, String> observed = new LinkedHashMap<Long, String>();
            for (ReadRow read : reads) {
                WriteRow write = corpus.writeOf(session, entry.getKey(),
                        read.observedVersion());
                if (write == null) {
                    outside = true;
                } else {
                    observed.put(write.version(),
                            write.endpoint().occurrence().id());
                }
            }
            List<String> observedPin = new ArrayList<String>();
            if (outside) {
                for (String symbol : symbols) {
                    String pin = pins.get(symbol);
                    if (pin != null && !observedPin.contains(pin)) {
                        observedPin.add(pin);
                    }
                }
            }
            // One arm is the run's own interleaving: the join says it.
            if (found.size() + (observedPin.isEmpty() ? 0 : 1) < 2) continue;
            if (observedPin.isEmpty()) {
                observedWrites.put(entry.getKey(), observed);
            } else {
                observedPins.put(entry.getKey(), observedPin);
            }
            List<String> writers = new ArrayList<String>();
            for (Arms.Arm arm : found) {
                String writer = arm.producer().id();
                if (!writers.contains(writer)) writers.add(writer);
                add(outsOfWriter, writer, new Out(arm, symbols));
            }
            writersOf.put(entry.getKey(), writers);
        }
        // One selector per writer occurrence, its body stated once.
        Map<String, String> selectorOf = new LinkedHashMap<String, String>();
        for (Map.Entry<String, List<Out>> writer
                : outsOfWriter.entrySet()) {
            String name = "writer_arm__" + ordinal + "__"
                    + ArtifactIO.digest(writer.getKey() + "|" + session, 12);
            lowering.declare(name, VmTermLowering.Sort.BOOL);
            String body = producerBody(ordinal, selector, writer.getKey(),
                    session, writer.getValue(), reached,
                    new ArrayList<String>(), new LinkedHashSet<String>(), 0);
            if (body == null) continue;
            selectorOf.put(writer.getKey(), name);
            String assertion = "writer_family__" + ordinal + "__"
                    + ArtifactIO.digest(writer.getKey() + "|" + session, 12);
            String formula = "(=> " + name + " " + body + ")";
            stated.add(formula);
            lowering.assertNamed(assertion,
                    "(=> " + selector + " " + formula + ")");
            armChoices.put(name, ArmChoice.of(assertion,
                    writer.getKey(), Collections.<String>emptyList(),
                    session, armsOf(writer.getValue())));
        }
        // And one exactly-one per location, over the writers it has.
        for (Map.Entry<String, List<String>> location
                : writersOf.entrySet()) {
            List<String> selectors = new ArrayList<String>();
            for (String writer : location.getValue()) {
                String name = selectorOf.get(writer);
                if (name != null) selectors.add(name);
            }
            List<String> observedPin = observedPins.get(location.getKey());
            // A refused body can leave one arm, which is no alternative: the
            // reads keep their own joins, not a selector nothing forces.
            if (selectors.size() + (observedPin == null ? 0 : 1) < 2) {
                continue;
            }
            // The arm the run took: the pins', else the one write every read
            // of it observed.
            Map<Long, String> observed =
                    observedWrites.get(location.getKey());
            String taken = observed != null && observed.size() == 1
                    ? selectorOf.get(observed.values().iterator().next())
                    : null;
            if (observedPin != null) {
                String name = "observed_arm__" + ordinal + "__"
                        + ArtifactIO.digest(location.getKey() + "|"
                        + session, 12);
                lowering.declare(name, VmTermLowering.Sort.BOOL);
                String assertion = "observed_family__" + ordinal + "__"
                        + ArtifactIO.digest(location.getKey() + "|"
                        + session, 12);
                String formula = "(=> " + name + " "
                        + VmTermLowering.and(observedPin) + ")";
                stated.add(formula);
                lowering.assertNamed(assertion,
                        "(=> " + selector + " " + formula + ")");
                armChoices.put(name, ArmChoice.of(assertion,
                        "observed:" + location.getKey(),
                        Collections.<String>emptyList(), session,
                        Collections.<Arms.Arm>emptyList()));
                selectors.add(name);
                taken = name;
            }
            for (ReadRow read : byLocation.get(location.getKey())) {
                chosen.add(read.symbol());
            }
            if (taken == null) {
                String saw = observed.size() == 1
                        ? "one write, by " + observed.values().iterator()
                        .next() + ", that no arm here states"
                        : "versions " + observed.keySet() + " while one arm "
                        + "binds every read";
                gaps.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.BLOCKING, location.getKey(), "path "
                                + path.pathId + " observed " + saw + ": no "
                                + "arm is the pairing the run took, so the "
                                + "run as it happened is no world of the "
                                + "formula"));
            } else if (!recorded.contains(taken)) {
                recorded.add(taken);
            }
            String formula = Arms.exactlyOne(selectors);
            stated.add(formula);
            lowering.assertNamed("state_family__" + ordinal + "__"
                            + ArtifactIO.digest(location.getKey(), 12),
                    "(=> " + selector + " " + formula + ")");
        }
        return chosen;
    }

    /** The arms one writer's outs were built from. */
    private static List<Arms.Arm> armsOf(List<Out> outs) {
        List<Arms.Arm> found = new ArrayList<Arms.Arm>();
        for (Out out : outs) found.add(out.arm);
        return found;
    }

    /**
     * One row's expression, lowered in its OWN session's scope: its
     * identities and reads belong to that execution, not the consumer's.
     * What that lowering requires of the value -- its definedness, the
     * recorded readings and container requires beneath it -- goes into
     * {@code conditions}, to be conjoined wherever the value is; without
     * them the value is free of what the run established about it.  Null
     * {@code conditions}: only the value's sort is asked.
     */
    Term lower(String session, String expressionRef, String origin,
               List<String> conditions) {
        SessionReader reader = corpus.session(session);
        if (reader == null) return null;
        JsonObject expression = reader.expressions()
                .expression(expressionRef);
        if (expression == null) {
            // A row cites an expression the corpus does not hold.
            composer.gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING, expressionRef,
                    "a row of session " + session + " cites an expression "
                            + "its session's table does not hold");
            return null;
        }
        lowering.begin(session, corpus.join(session),
                reader.expressions());
        Term value = lowering.term(expressionRef, origin);
        List<String> refused = new ArrayList<String>(
                lowering.openRefusals());
        List<String> required = lowering.end();
        if (!refused.isEmpty()) {
            for (String refusal : refused) {
                composer.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, refusal,
                        "an arm of this corpus rests on a value the "
                                + "recording does not state");
            }
            return null;
        }
        if (conditions != null) conditions.addAll(required);
        return value;
    }
}
