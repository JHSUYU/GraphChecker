package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Term;

import edu.uva.liftlab.graphchecker.contract.Arm;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.Family;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.explore.Corpus;
import edu.uva.liftlab.graphchecker.explore.SlotTable;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.smtLiteral;

/**
 * THE FAMILIES of one composition: which deliveries a slot had, in SMT.
 *
 * <p>Relocated out of {@link Composer} unchanged -- the same bodies, the
 * same order, no rule altered.  {@code Arms} decides what an arm IS; this
 * decides how the alternatives of one slot read in a query, which is all a
 * composer should own of them: the WIRE families of the interactions a path
 * reaches ({@link #closeFamilies}), the STATE families of the reads a
 * writer occurrence could have delivered otherwise
 * ({@link #stateFamilies}), the rendering of one arm with its prefix and
 * its guard ({@link #render}), and the rows that say which slots this
 * anchor had no use for.</p>
 *
 * <p>It holds the composition's own collections rather than copies: a
 * family registered here is a family of that composition's manifest, and
 * the gap rows it raises are that composition's ledger.  The three things
 * that stay with {@link Composer} are reached through it -- the gap
 * writer, the free-symbol test, and this epoch's slot table, which the
 * composer assigns while it runs.</p>
 */
final class ComposedFamilies {

    private final Composer composer;
    private final Corpus corpus;
    private final OccurrenceAddress anchor;
    private final Arms arms;
    private final SmtLowering lowering;
    private final Map<String, Family> families;
    private final Map<String, Set<String>> unattestedRoots;
    private final Set<String> replacing;
    private final Set<String> slotNamed;
    private final Set<String> unpairedNamed;
    private final Set<String> aliasingNamed;
    private final List<GapRow> gaps;

    ComposedFamilies(Composer composer, Corpus corpus,
                     OccurrenceAddress anchor, Arms arms,
                     SmtLowering lowering, Map<String, Family> families,
                     Map<String, Set<String>> unattestedRoots,
                     Set<String> replacing, Set<String> slotNamed,
                     Set<String> unpairedNamed, Set<String> aliasingNamed,
                     List<GapRow> gaps) {
        this.composer = composer;
        this.corpus = corpus;
        this.anchor = anchor;
        this.arms = arms;
        this.lowering = lowering;
        this.families = families;
        this.unattestedRoots = unattestedRoots;
        this.replacing = replacing;
        this.slotNamed = slotNamed;
        this.unpairedNamed = unpairedNamed;
        this.aliasingNamed = aliasingNamed;
        this.gaps = gaps;
    }

    /**
     * WHICH DELIVERY a family's selector stands for.
     *
     * <p>The manifest's answer to "which arm did the witness take": a
     * selector the model set is one slot's one delivery, and without this
     * the claim names a mechanism whose evidence is thirteen anonymous
     * disjuncts.</p>
     */
    public static final class ArmChoice {
        private final String family;
        private final String groupId;
        private final List<String> attachEndpointIds;
        private final String sessionId;
        private final String producerPathId;
        private final List<String> interactionIds;
        private final List<String> expressionRefs;
        private final boolean attested;

        private ArmChoice(String family, String groupId,
                          List<String> attachEndpointIds, String sessionId,
                          String producerPathId,
                          List<String> interactionIds,
                          List<String> expressionRefs, boolean attested) {
            this.family = family;
            this.groupId = groupId;
            this.attachEndpointIds = Collections.unmodifiableList(
                    attachEndpointIds);
            this.sessionId = sessionId;
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
                    session, path, slots, refs, attested);
        }

        /** The named assertion this arm-set is one case of. */
        public String family() {
            return family;
        }

        /**
         * WHAT this selector stands for having been produced by one run:
         * the message, spelled by the leaves it was received at, or a
         * writer occurrence for a state family.
         */
        public String groupId() {
            return groupId;
        }

        /** The attach endpoints one message was received at. */
        public List<String> attachEndpointIds() {
            return attachEndpointIds;
        }

        /** The run that made it. */
        public String sessionId() {
            return sessionId;
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

    /** The declared roots one lowered expression mentions. */
    private Set<String> declaredRootsIn(String term) {
        Set<String> found = new LinkedHashSet<String>();
        for (Map.Entry<String, List<RootMintRow>> entry
                : corpus.roots().entrySet()) {
            RootMintRow row = corpus.anyRoot(entry.getKey());
            if (row == null || !row.declared()) continue;
            if (SmtLowering.mentions(term, row.symbol())) {
                found.add(row.rootId());
            }
        }
        return found;
    }


    /**
     * ONE SELECTOR PER (MESSAGE, SESSION), for every arrival this path
     * binds.
     *
     * <p>RULE 3 of the minimal delta, and the unit is THE MESSAGE THE PATH
     * RECEIVED: the attaches of one arrival carry one correlation id, and
     * every leaf of that arrival was produced by one run of the producer.
     * So the arms of the interactions a message covers are grouped by that
     * message and by the session that made it, the group's bindings, guard
     * and closure are stated once under one selector, and exactly one of
     * the ELIGIBLE sessions of that message holds.</p>
     *
     * <p>Grouping by PRODUCER OCCURRENCE instead is not enough, and 11741
     * is why: {@code PBHelper.convert(ExportedBlockKeys)} converts each
     * block key in a loop, the loop body's iteration is part of the
     * occurrence's execution index, so the five exported leaves of ONE
     * response are five occurrences.  Per occurrence they are five
     * independent choices and a model answered them 182906, 182908,
     * 182908, 182907 out of an export that held 182905, 182906, 182907,
     * 182908 -- one id twice, and the id the target looks up nowhere.  Per
     * MESSAGE they are one choice: one run made that response, and a
     * witness reads the response that run made or another run's, never
     * halves of both.</p>
     *
     * <p>A wire arrival is bound HERE and nowhere else (CLOSURE-V2): the
     * path states no arrival of its own, so a message no session of this
     * corpus could have sent leaves its {@code v_H} free, and that is
     * refused by name rather than pinned to what this session happened to
     * receive.</p>
     *
     * @return whether every message this path binds has an eligible
     *         session; a path with one that has none leaves the disjunction
     */
    boolean closeFamilies(int ordinal, String selector, Set<String> reached,
                          List<AttachRow> bound, List<String> stated,
                          List<GapRow> refusals) {
        return closeMessages(ordinal, selector, bound, reached, stated,
                refusals, new LinkedHashSet<String>(), 0);
    }

    /** How deep one delivery may be handed on before this refuses. */
    private static final int NESTING_LIMIT = 16;

    /**
     * The message groups of one set of attaches, under one guard.
     *
     * <p>Called with the path's own selector for the attaches the path
     * bound, and with a {@code (message, S)} selector's family guard for
     * the attaches S's own delivery was itself handed (R3b iv) -- the same
     * rule at every depth, grouped by the DELIVERING session's own
     * correlation ids, because "which message did this rest on" is the same
     * question one hop back.  A message already closed at an outer level is
     * not closed again: its selector already binds every leaf of it.</p>
     */
    private boolean closeMessages(int ordinal, String guard,
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
        // (1) THE MESSAGES: the path's attaches by correlation id, which is
        //     the within-run pairing evidence one arrival carries on every
        //     leaf of it.  An attach whose row states no correlation is a
        //     message of its own -- nothing says it came in with another.
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
            // (2) The arms of each leaf, one hop deep, and which sessions
            //     attest a delivery at it.
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
            if (!messageFamily(ordinal, guard, message.getKey(), leaves,
                    slotOf, symbolOf, eligible, bySession, reached, stated,
                    refusals, closedGroups, depth)) {
                return false;
            }
        }
        return true;
    }

    /** One message's identity: the leaves it was received at. */
    private static String groupId(List<AttachRow> leaves) {
        List<String> ids = new ArrayList<String>();
        for (AttachRow attach : leaves) {
            if (!ids.contains(attach.endpoint().id())) {
                ids.add(attach.endpoint().id());
            }
        }
        Collections.sort(ids);
        return String.join("|", ids);
    }

    /**
     * R3c': the sessions that could have SENT this message.
     *
     * <p>A session is an option for a message only if it has an attested
     * arm at every interaction the message covers.  A run that exported
     * four entries is not an option for a path that attached five: taking
     * it would leave the fifth arrival bound by a run that never sent it,
     * which is the mixed response rule 3 exists to forbid.  This replaces
     * the per-family "did any arm of this corpus fill the slot" check,
     * which asked the question one leaf at a time and so answered yes for
     * every leaf of a partial response.</p>
     *
     * @return the eligible sessions, or null when none is -- the path is
     *         then refused by name and leaves the disjunction
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
     * ONE MESSAGE, as a finite case split over the runs that could have
     * sent it.
     *
     * <p>{@code sel_{M,S} => (guard_S /\ closure_{M,S} /\ v_H_k = e_{k,S}
     * for every leaf k)} and exactly-one over the eligible sessions: the
     * same constraint a per-leaf split stated, and the one a solver can
     * decide by CASES rather than by searching the union of every leaf's
     * arms at once -- and the only one a model can be asked which RUN's
     * response the witness rests on.</p>
     */
    private boolean messageFamily(
            int ordinal, String guard, String message,
            List<AttachRow> leaves, Map<String, Interaction> slotOf,
            Map<String, String> symbolOf, List<String> eligible,
            Map<String, List<Arms.Arm>> bySession, Set<String> reached,
            List<String> stated, List<GapRow> refusals,
            Set<String> closedGroups, int depth) {
        String group = groupId(leaves);
        String name = "message_family__" + ordinal + "__"
                + ArtifactIO.digest(group, 12);
        List<String> selectors = new ArrayList<String>();
        List<String> cases = new ArrayList<String>();
        for (String session : eligible) {
            List<Arms.Arm> held = oneArmPerLeaf(bySession.get(session),
                    message, session);
            if (held == null || held.isEmpty()) continue;
            String selector = "message_arm__" + ordinal + "__"
                    + ArtifactIO.digest(group + "|" + session, 12);
            // Declared BEFORE the body is built: the nested families the
            // body opens are asserted under this name, and they stay
            // asserted even where the arm-set is then refused -- a name an
            // assertion holds and nothing declares makes z3 answer the
            // whole query with an error instead of a verdict.
            lowering.declare(selector, VmTermLowering.Sort.BOOL);
            List<String> nested = new ArrayList<String>();
            String body = producerBody(ordinal, selector, guard, message,
                    session, bindings(held), reached, nested, closedGroups,
                    depth);
            if (body == null) continue;
            selectors.add(selector);
            cases.add("(=> " + selector + " " + body + ")");
            stated.addAll(nested);
            armChoices.put(selector, ArmChoice.of(name, group,
                    endpointIds(leaves), session, held));
        }
        if (selectors.isEmpty()) {
            refusals.add(GapRow.of(corpus.seedSessionId(),
                    GapKind.UNPRODUCIBLE_ANSWER, GapClass.DIAGNOSTIC,
                    message, "every session eligible to have sent this "
                            + "message rests on a value the recording does "
                            + "not state, so nothing binds what this path "
                            + "read from it"));
            return false;
        }
        for (Map.Entry<String, Interaction> slot : slotOf.entrySet()) {
            reached.add(slot.getKey());
            slotOpened(slot.getKey(), slot.getValue());
            List<Arm> rows = new ArrayList<Arm>();
            for (String session : eligible) {
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
     * ONE delivery per leaf, and a refusal when the rows state two.
     *
     * <p>The selector binds every leaf of this message at once, so two arms
     * of one session at one leaf would be conjoined -- {@code v = e1} and
     * {@code v = e2} -- and a witness would need the two expressions to be
     * equal.  Identical rows are one delivery stated twice and are dropped;
     * two DIFFERENT expressions at one leaf of one run are a thing the
     * recording says and this cannot compose, so the whole {@code (message,
     * S)} arm-set is refused by name.  (The text dedup this replaces was
     * blind to which leaf an arm filled, so one session's arm could stand
     * in for another's wherever the two rendered alike.)</p>
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
     * R3b: AN ARM IS CLOSED LIKE A PATH.
     *
     * <p>Under {@code sel_{P,S}}, in S's own scope, four things and never
     * the anchor's:</p>
     *
     * <ol>
     *   <li>{@code pi_{P,S}}: P's decisions before the LAST of the
     *       deliveries this path takes from it -- what that run had decided
     *       by the time it produced them, never after.</li>
     *   <li>the closure of P in S: the same row-level fixed point the
     *       anchor gets, started at P at that cutoff, plus the container
     *       VERSIONS the delivered expressions read
     *       ({@link #expressionWrites}).  A delivery is what the producer
     *       had in hand, and what it had in hand is every earlier mutation
     *       of the state it read.</li>
     *   <li>the prefixes of everything that closure reached, and the state
     *       joins of their reads -- through the same routines the path
     *       uses, so a decision and a join mean the same thing wherever
     *       they stand.  Only the joins this arm's own text REACHES: an
     *       unreached join binds a fresh variable, which constrains nothing
     *       and drags its whole theory into the query.</li>
     *   <li>P's own attaches, as nested families under this same selector
     *       (R3b iv), recursively by this rule.</li>
     * </ol>
     *
     * <p>Without (i)-(iii) an arm said WHAT was delivered and not why: on
     * hdfs-11741 the NameNode's export of its key set rests on the removal
     * scan of the previous tick, under a comparison against the clock that
     * scan read, and no conjunct of any composed query named that clock.</p>
     *
     * @return the arm-set's conjunction, or null when a value it rests on
     *         is not stated -- which refuses this {@code (P, S)} and not
     *         the path
     */
    private String producerBody(int ordinal, String selector,
                                String nestedGuard, String subject,
                                String session,
                                List<Out> outs, Set<String> reachedSlots,
                                List<String> nestedStated,
                                Set<String> closedProducers, int depth) {
        List<GapRow> local = new ArrayList<GapRow>();
        SmtLowering.SessionJoin rows =
                SmtLowering.joinOf(corpus.session(session));
        lowering.begin(session, rows, corpus.expressions(session));
        List<String> conjuncts = new ArrayList<String>();
        boolean stated = true;
        // The bindings: what this run delivered at each out.
        Map<String, String> guards = new LinkedHashMap<String, String>();
        for (Out out : outs) {
            Term delivered = lower(session, out.arm.expressionRef(),
                    "arm:" + out.arm.slotId());
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
            // The name has to be IN the query.  A guard names a root the
            // arm's own expression need not mention -- the delivering
            // replay's valuation of every varied root is part of what the
            // delivery happened under -- and asserting an equality over a
            // constant nothing declares makes z3 answer the whole query
            // with an error instead of a verdict.
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
            // THE CLOSURE OF EVERY OCCURRENCE THIS GROUP CAME OUT OF, each
            // started at its OWN delivery: one message can be produced by
            // several occurrences of one run -- five leaf occurrences of
            // one convert(ExportedBlockKeys) loop -- and each of them had
            // decided what it had decided by the time IT delivered.  The
            // reached sets are merged at the widest cutoff per occurrence
            // and the conditions are stated once.
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
            Set<String> answered = new LinkedHashSet<String>();
            composer.statedReads(session, reached.keySet(), local, joins,
                    answered);
            composer.stateJoins(session, reached.keySet(), rows, local,
                    new ArrayList<ReadRow>(), new ArrayList<String>(),
                    joins, answered);
            conjuncts.addAll(composer.closureConditions(session, reached,
                    local));
            // UNDER THIS FAMILY'S OWN GUARD, not under this one session's
            // selector.  Several sessions of one occurrence can forward the
            // SAME handoff variable -- the VM symbol is the leaf's, not the
            // run's -- and a nested family opened under the first of them
            // leaves that variable referenced by the others and bound by
            // nothing: hdfs-11741 campaign #2 came back with the DataNode's
            // `addKeys` arrival at 2, a value no session delivered, while
            // its own family sat under a selector the model had set false.
            stated = closeMessages(ordinal, nestedGuard,
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
     * The attaches one delivery was itself handed (R3b iv).
     *
     * <p>{@link Arms.Arm#nested} names the handoff variables inside the
     * delivered expression; the rows of the DELIVERING session say which
     * attach each one came from, and those attaches are closed under this
     * delivery's own selector, because they are only referenced when this
     * delivery is the one taken.</p>
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
     * The container VERSIONS a delivered expression reads.
     *
     * <p>An expression that projects a value out of shared state names the
     * read it made -- its location and the event id it read at -- and not
     * the write that produced that state.  The closure needs the write: the
     * latest version of that location at or before the read is the state
     * the producer had in hand, and its writer's prefix is a reason the
     * delivery is what it is.  On hdfs-11741 the NameNode's export reads
     * its key map at event 599; the write it rests on is version 589, the
     * last of the previous tick, and without this edge the removal scan
     * that ran between the ticks is in no closure and the clock it read is
     * declared nowhere.</p>
     */
    private List<WriteRow> expressionWrites(String session, List<Out> outs) {
        List<WriteRow> writes = new ArrayList<WriteRow>();
        Set<String> seen = new LinkedHashSet<String>();
        SessionReader reader = corpus.session(session);
        if (reader == null) return writes;
        for (Out out : outs) {
            JsonObject expression = reader.expressions()
                    .expression(out.arm.expressionRef());
            if (expression == null) continue;
            Map<String, Long> read = new LinkedHashMap<String, Long>();
            readNodes(expression, read, 0);
            for (Map.Entry<String, Long> each : read.entrySet()) {
                WriteRow latest = null;
                for (WriteRow write : corpus.writesOf(session,
                        each.getKey())) {
                    if (write.version() > each.getValue().longValue()) {
                        continue;
                    }
                    if (latest == null
                            || latest.version() < write.version()) {
                        latest = write;
                    }
                }
                if (latest == null) continue;
                if (!seen.add(each.getKey() + "#" + latest.version())) {
                    continue;
                }
                writes.add(latest);
            }
        }
        return writes;
    }

    /** How deep one expression is walked for the reads inside it. */
    private static final int EXPRESSION_DEPTH = 64;

    /**
     * Location -> the latest event id this expression read it at.
     *
     * <p>Every node that carries both a {@code location} and a
     * {@code readEventId} states a read of shared state, whatever else the
     * node is -- which is what a {@code ReadFromExpression} and the
     * {@code ConsumerBoundaryExpression} over one are.</p>
     */
    private static void readNodes(JsonElement expression,
                                  Map<String, Long> into, int depth) {
        if (expression == null || depth > EXPRESSION_DEPTH) return;
        if (expression.isJsonArray()) {
            for (JsonElement each : expression.getAsJsonArray()) {
                readNodes(each, into, depth + 1);
            }
            return;
        }
        if (!expression.isJsonObject()) return;
        JsonObject node = expression.getAsJsonObject();
        JsonElement location = node.get("location");
        JsonElement at = node.get("readEventId");
        if (location != null && location.isJsonObject() && at != null
                && at.isJsonPrimitive()) {
            String key = SmtLowering.locationKey(location.getAsJsonObject());
            long event = at.getAsLong();
            Long held = into.get(key);
            if (held == null || held.longValue() < event) {
                into.put(key, Long.valueOf(event));
            }
        }
        for (Map.Entry<String, JsonElement> member : node.entrySet()) {
            readNodes(member.getValue(), into, depth + 1);
        }
    }

    /**
     * An arm whose producer ran concretely: what it delivered is stated and
     * why is not, so it is no option for that occurrence and no witness may
     * move a root inside it.
     */
    private void noteUnattested(Arms.Arm arm, String detail) {
        Set<String> held = unattestedRoots.get(arm.slotId());
        if (held == null) {
            held = new LinkedHashSet<String>();
            unattestedRoots.put(arm.slotId(), held);
        }
        SessionReader reader = corpus.session(arm.sessionId());
        JsonObject expression = reader == null ? null
                : reader.expressions().expression(arm.expressionRef());
        Set<String> symbols = new LinkedHashSet<String>();
        if (expression != null) Arms.symbolsIn(expression, symbols, 0);
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
     * Every arm {@link Arms} refused since the last drain (R4 item 3), filed
     * as this composition's own gap.
     *
     * <p>{@code Arms} states WHICH arm it refused and why; the stage that
     * asked for the arms is the stage that has a gap list, so the refusal is
     * drained and filed here and never left to be counted twice by the next
     * question.</p>
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
        List<T> held = index.get(key);
        if (held == null) {
            held = new ArrayList<T>();
            index.put(key, held);
        }
        held.add(value);
    }

    /**
     * Every interaction the corpus records that this anchor does not reach.
     *
     * <p>Recorded, never a refusal: an interaction outside the anchor's
     * closure says nothing about this anchor's disjunction, and a run that
     * exercised more of the system than this question needs has not gone
     * wrong.  It is named so that a reader comparing the skeleton with the
     * rows can see which pairs the composition had no use for.</p>
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
     * An attach whose producer the recording does not name.
     *
     * <p>Two different absences, and the row says which.  A producer
     * endpoint that exists but could not be addressed in full is
     * LINEAGE_LOST -- the interaction is there and the naming failed.  An
     * attach with no producer at all is an UNSTATED_VALUE: the recording
     * does not say the delivery happened, only that a value arrived.</p>
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
     * THE STATE FAMILIES, by the same rule with the WRITER as P.
     *
     * <p>Rule 3 again: a writer occurrence's writes move as a BLOCK, so one
     * selector stands for that occurrence having been the writer, and it
     * binds every read of every location this path joins to it -- with that
     * occurrence's prefix, closure and joins stated once beneath it.  Then
     * one exactly-one PER LOCATION over the writers of that location: a
     * location with a single writer says nothing a join has not said and
     * gets none.</p>
     *
     * <p>A selector shared across two of one occurrence's locations is the
     * point of the rule, not a side effect: choosing that occurrence as the
     * writer of one location and not of the other is an interleaving in
     * which half of a block moved.</p>
     */
    Set<String> stateFamilies(Corpus.RecordedPath path,
                              int ordinal, String selector,
                              List<ReadRow> joined,
                              Set<String> reached,
                              List<String> stated) {
        String session = path.sessionId;
        Set<String> chosen = new LinkedHashSet<String>();
        // One choice per (reader occurrence, location): a writer's writes to
        // it move as a BLOCK, and every read of that location inside this
        // occurrence takes the same arm -- never a writer interposed between
        // two reads of one occurrence.
        Map<String, List<ReadRow>> byLocation =
                new LinkedHashMap<String, List<ReadRow>>();
        for (ReadRow read : joined) {
            add(byLocation, SmtLowering.locationKey(read.location()), read);
        }
        // Which writer occurrences each location has, and what each one of
        // them binds across ALL the locations it writes.
        Map<String, List<String>> writersOf =
                new LinkedHashMap<String, List<String>>();
        Map<String, OccurrenceAddress> writerOf =
                new LinkedHashMap<String, OccurrenceAddress>();
        Map<String, List<Out>> outsOfWriter =
                new LinkedHashMap<String, List<Out>>();
        for (Map.Entry<String, List<ReadRow>> entry
                : byLocation.entrySet()) {
            List<ReadRow> reads = entry.getValue();
            // Alternatives need an owner that NAMES the storage
            // ({@link Arms#namedOwner}).  A class on a heap location is
            // every instance of it at once, which turns "another writer of
            // L" into "a writer of something else", so such a read keeps
            // the delivery its own run gave it and is named here.
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
                // The OBSERVED writer is stated whatever it is -- it is
                // what the run did -- so an unattested one reaches the
                // formula, and no witness may move a root inside it.
                if (!arm.attested()) {
                    noteUnattested(arm, "the arm states what it wrote and "
                            + "not why, so no witness may move a root "
                            + "inside it");
                }
                // Reached and recorded whether or not a case split
                // follows: WHICH writers a location had is what the rows
                // state, and the unattested-arm gate reads this set.
                reached.add(arm.slotId());
                families.put(arm.slotId(), Family.of(arm.slotId(),
                        Collections.singletonList(row(arm))));
                found.add(arm);
            }
            fileRefusals();
            // One arm is the run's own interleaving and says nothing the
            // join has not already said.
            if (found.size() < 2) continue;
            chosen.addAll(symbols);
            List<String> writers = new ArrayList<String>();
            for (Arms.Arm arm : found) {
                String writer = arm.producer().id();
                writerOf.put(writer, arm.producer());
                if (!writers.contains(writer)) writers.add(writer);
                add(outsOfWriter, writer, new Out(arm, symbols));
            }
            writersOf.put(entry.getKey(), writers);
        }
        // One selector per writer occurrence, its body stated once.
        Map<String, String> selectorOf = new LinkedHashMap<String, String>();
        for (Map.Entry<String, List<Out>> writer
                : outsOfWriter.entrySet()) {
            OccurrenceAddress at = writerOf.get(writer.getKey());
            String name = "writer_arm__" + ordinal + "__"
                    + ArtifactIO.digest(writer.getKey() + "|" + session, 12);
            lowering.declare(name, VmTermLowering.Sort.BOOL);
            String body = producerBody(ordinal, name, selector,
                    writer.getKey(), session, writer.getValue(), reached,
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
            if (selectors.size() < 2) continue;
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
     * One export's expression, lowered in its own session's scope.
     *
     * <p>Its own session: the identities inside it are that execution's
     * objects, and the reads inside it join to that execution's write log.
     * An arm lowered in the consumer's scope would state one replay's
     * history of another replay's objects.</p>
     */
    Term lower(String session, ExportRow export, String origin) {
        return lower(session, export.expressionRef(), origin);
    }

    Term lower(String session, String expressionRef, String origin) {
        SessionReader reader = corpus.session(session);
        if (reader == null) return null;
        JsonObject expression = reader.expressions()
                .expression(expressionRef);
        if (expression == null) {
            // Same inconsistency as the state join's, and the same class:
            // a row of this corpus cites an expression the corpus does not
            // contain, so what it stands for is not composable from these
            // sessions at all.
            composer.gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING, expressionRef,
                    "a row of session " + session + " cites an expression "
                            + "its session's table does not hold");
            return null;
        }
        lowering.begin(session,
                SmtLowering.joinOf(corpus.session(session)));
        Term value = lowering.term(expression, null, origin);
        List<String> refused = new ArrayList<String>(
                lowering.openRefusals());
        lowering.end();
        if (value == null || !refused.isEmpty()) {
            for (String refusal : refused) {
                composer.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, refusal,
                        "an arm of this corpus rests on a value the "
                                + "recording does not state");
            }
            return null;
        }
        return value;
    }
}
