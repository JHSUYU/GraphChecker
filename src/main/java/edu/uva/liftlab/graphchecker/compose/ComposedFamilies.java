package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Term;

import edu.uva.liftlab.graphchecker.contract.Arm;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.Family;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.explore.Corpus;
import edu.uva.liftlab.graphchecker.explore.SlotTable;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.Z3;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
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
 * composition's own collections, not copies, into which one path's families
 * go whole or not at all ({@link #discard}), and reaches {@link Composer}
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
        private final List<SmtLowering.StateChoice> states;
        private final Map<String, BoundHole> holes;

        private ArmChoice(String family, String groupId,
                          List<String> attachEndpointIds,
                          List<String> sessionIds, String producerPathId,
                          List<String> interactionIds,
                          List<String> expressionRefs, boolean attested,
                          List<SmtLowering.StateChoice> states,
                          Map<String, BoundHole> holes) {
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
            this.states = Collections.unmodifiableList(states);
            this.holes = Collections.unmodifiableMap(holes);
        }

        static ArmChoice of(String family, String groupId,
                            List<String> attachEndpointIds, String session,
                            List<Arms.Arm> arms, Map<String, BoundHole> holes) {
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
                            session)), path, slots, refs, attested,
                    Collections.<SmtLowering.StateChoice>emptyList(), holes);
        }

        /** The same arm, stated by one more run. */
        ArmChoice alsoBy(String session) {
            List<String> sessions = new ArrayList<String>(sessionIds);
            sessions.add(session);
            return new ArmChoice(family, groupId, attachEndpointIds,
                    sessions, producerPathId, interactionIds,
                    expressionRefs, attested, states, holes);
        }

        /** The same arm, with the states of the objects its stores deliver
         *  a query through the read may see ({@link #states}). */
        ArmChoice seeing(List<SmtLowering.StateChoice> seen) {
            return new ArmChoice(family, groupId, attachEndpointIds,
                    sessionIds, producerPathId, interactionIds,
                    expressionRefs, attested, seen, holes);
        }

        /** The same arm, with only the states a model's nested selectors
         *  chose ({@code true} in {@code model}). */
        ArmChoice taking(Map<String, String> model) {
            List<SmtLowering.StateChoice> taken =
                    new ArrayList<SmtLowering.StateChoice>();
            for (SmtLowering.StateChoice state : states) {
                if ("true".equals(model.get(state.selector))) {
                    taken.add(state);
                }
            }
            return seeing(taken);
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

        /**
         * For a state arm, each state of the object a store it delivers
         * holds that a query through the read may be answered from
         * ({@link SmtLowering#stateChoices}); once a model is read
         * ({@link #taking}), the ones it chose.
         */
        public List<SmtLowering.StateChoice> states() {
            return states;
        }

        /**
         * The codec holes this arm binds, by consumer endpoint id: what a
         * model's valuation of each is checked against in CONFIRM
         * ({@link #holeTexts}).
         */
        public Map<String, BoundHole> holes() {
            return holes;
        }
    }

    /**
     * One codec hole an arm binds (WIRE-CODEC §6.5): its symbol and the
     * decoded leaf's {@code javaType} (a primitive or a String, invariant
     * 5), and whether the value it was bound to rests on a clock -- directly,
     * or through the {@code nested} holes its operand names.  A replay
     * reads its clocks afresh (CONFIRM holds a run to the model's edges
     * and roots, never to its instants), so only a value resting on no
     * clock is one a replay reproduces.
     */
    public static final class BoundHole {
        public final String symbol;
        public final String javaType;
        public final boolean clocked;
        public final Set<String> nested;

        BoundHole(String symbol, String javaType, boolean clocked,
                  Set<String> nested) {
            this.symbol = symbol;
            this.javaType = javaType;
            this.clocked = clocked;
            this.nested = Collections.unmodifiableSet(nested);
        }
    }

    /**
     * WHAT A REPLAY MUST DECODE AT EACH HOLE of these selected arms
     * (WIRE-CODEC §6.5): the model's valuation of the hole as the decoded
     * text -- an integral's decimal, a boolean's {@code true}/{@code
     * false}, a String's characters -- by consumer endpoint id, for every
     * hole whose value rests on no clock through the selected arms.  A
     * hole resting on a nested hole no selected arm binds, or a char or a
     * floating value (no decimal text the model states), is not stated.
     */
    public static Map<String, String> holeTexts(
            Collection<ArmChoice> selected, Map<String, String> model) {
        Map<String, BoundHole> bySymbol =
                new LinkedHashMap<String, BoundHole>();
        Map<String, String> consumerOf = new LinkedHashMap<String, String>();
        for (ArmChoice arm : selected) {
            for (Map.Entry<String, BoundHole> hole : arm.holes().entrySet()) {
                bySymbol.put(hole.getValue().symbol, hole.getValue());
                consumerOf.put(hole.getValue().symbol, hole.getKey());
            }
        }
        Map<String, String> texts = new LinkedHashMap<String, String>();
        for (Map.Entry<String, BoundHole> hole : bySymbol.entrySet()) {
            if (clocked(hole.getKey(), bySymbol,
                    new LinkedHashSet<String>())) {
                continue;
            }
            String value = model.get(hole.getKey());
            String text = value == null ? null
                    : text(hole.getValue().javaType, value);
            if (text != null) {
                texts.put(consumerOf.get(hole.getKey()), text);
            }
        }
        return texts;
    }

    /** A model's value as the text a hole of this type decodes, or null. */
    private static String text(String javaType, String value) {
        VmTermLowering.Sort sort = JavaSmtSorts.sortOfJava(javaType);
        if (sort == VmTermLowering.Sort.STRING) return Z3.javaString(value);
        return sort == VmTermLowering.Sort.BOOL
                || sort == VmTermLowering.Sort.INT && !"C".equals(javaType)
                ? value : null;
    }

    /** Whether a hole's value rests on a clock, or on what no arm binds. */
    private static boolean clocked(String symbol,
                                   Map<String, BoundHole> bySymbol,
                                   Set<String> seen) {
        BoundHole hole = bySymbol.get(symbol);
        if (hole == null || !seen.add(symbol)) return true;
        if (hole.clocked) return true;
        for (String nested : hole.nested) {
            if (clocked(nested, bySymbol, seen)) return true;
        }
        return false;
    }

    /** Arm selector -> the delivery it stands for. */
    private final Map<String, ArmChoice> armChoices =
            new LinkedHashMap<String, ArmChoice>();

    /** Every arm selector this composition declared, in the order made. */
    Map<String, ArmChoice> armChoices() {
        return Collections.unmodifiableMap(armChoices);
    }

    /*
     * ONE PATH'S FAMILIES ARE ALL OR NOTHING, AND SO IS ONE ARM'S.  What
     * closeFamilies and stateFamilies state for a path -- named assertions,
     * arm choices, families, the messages it closed -- goes into the
     * composition as it is made, so an accepted path's assertions keep
     * their place among the facts its lowering states, and is logged here
     * until the path is a disjunct (commit); a refused path's is taken back
     * (discard), and so is what a refused or duplicate arm's nested
     * families stated (rollback to the mark taken before its body).  Kept,
     * a path refused at its second message left the first message's family
     * under a selector no partition names, and the next path, composed at
     * the same ordinal, asserted that name again: z3 answers such a query
     * with an error (hdfs-17899-bug1 r1: 18 names defined twice, 52
     * dangling selectors).  An ordinal burnt per attempted path instead
     * would still leave the refused path's assertions and arms in the
     * query and the manifest.
     */
    private final List<String> pathAssertions = new ArrayList<String>();
    /** Every other change of the path being composed, undone in reverse. */
    private final List<Runnable> pathUndo = new ArrayList<Runnable>();
    /** The path being composed: its selector, and its messages by group. */
    private String path;
    private final Map<String, Closed> closed =
            new LinkedHashMap<String, Closed>();

    /**
     * ONE MESSAGE OF THE PATH, CLOSED ONCE (one family, one name), under
     * what rests on it: the path's selector for the path's own messages;
     * for a message a delivery was itself handed, every arm whose
     * conjunction names its handoffs, so it holds when one of them is
     * chosen and an arm not chosen imposes nothing (hdfs-11741 m1: another
     * run's six-key export, nested under the path, contradicted the path's
     * own run's five-key export in 234 of 235 paths).  Copies per arm
     * instead are a family per arm per level: hdfs-11741 i1's body ran an
     * 8 GB heap out.
     */
    private static final class Closed {
        final String name;
        final boolean atPath;
        final List<String> needers = new ArrayList<String>();
        /** Its exactly-one and cases, once closed. */
        String formula;
        List<String> selectors;

        Closed(String name, boolean atPath) {
            this.name = name;
            this.atPath = atPath;
        }
    }

    /**
     * The path is a disjunct: what its families stated stands, and each
     * message closed for an arm is asserted under the arms resting on it,
     * its own arms chosen only with one of them, so a model's true arm
     * selectors are the chain its path took and nothing beside it.
     */
    void commit() {
        for (Closed message : closed.values()) {
            if (message.atPath) continue;
            String needed = VmTermLowering.or(message.needers);
            assertFamily(message.name, "(=> " + path + " " + VmTermLowering
                    .and(Arrays.asList("(=> " + needed + " "
                            + message.formula + ")", "(=> " + VmTermLowering
                            .or(message.selectors) + " " + needed + ")"))
                    + ")");
        }
        pathAssertions.clear();
        pathUndo.clear();
        closed.clear();
        path = null;
    }

    /** The path is refused: nothing its families stated stays. */
    void discard() {
        rollback(new int[2]);
        path = null;
    }

    /** How far the path being composed has stated, for {@link #rollback}. */
    private int[] mark() {
        return new int[]{pathAssertions.size(), pathUndo.size()};
    }

    /** Takes back what the path stated since {@code mark}. */
    private void rollback(int[] mark) {
        List<String> assertions =
                pathAssertions.subList(mark[0], pathAssertions.size());
        lowering.retract(assertions);
        assertions.clear();
        List<Runnable> undo = pathUndo.subList(mark[1], pathUndo.size());
        for (int at = undo.size() - 1; at >= 0; at--) undo.get(at).run();
        undo.clear();
    }

    /** One named assertion of the path being composed. */
    private void assertFamily(String name, String formula) {
        lowering.assertNamed(name, formula);
        pathAssertions.add(name);
    }

    /** One arm selector of the path being composed, and what it stands for. */
    private void choose(String selector, ArmChoice choice) {
        ArmChoice before = armChoices.put(selector, choice);
        pathUndo.add(() -> restore(armChoices, selector, before));
    }

    /** One slot's family as the path being composed states it. */
    private void family(String slotId, Family family) {
        Family before = families.put(slotId, family);
        pathUndo.add(() -> restore(families, slotId, before));
    }

    /** One more thing resting on a message the path closed. */
    private void needs(Closed message, String guard) {
        message.needers.add(guard);
        pathUndo.add(() -> message.needers.remove(
                message.needers.size() - 1));
    }

    private static <T> void restore(Map<String, T> map, String key,
                                    T before) {
        if (before == null) {
            map.remove(key);
        } else {
            map.put(key, before);
        }
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
        path = selector;
        return closeMessages(ordinal, selector, owner, bound, reached,
                stated, refusals, 0);
    }

    /** How deep one delivery may be handed on before this refuses. */
    private static final int NESTING_LIMIT = 16;

    /**
     * The message groups of one set of attaches, resting on one GUARD: the
     * path selector for the path's own attaches, the selector of the ARM a
     * delivery is for the attaches it was itself handed (item (iv) of
     * {@link #producerBody}) -- the same rule at every depth.  A message the
     * path closed already only gains the guard as one more thing resting on
     * it ({@link Closed}); this level's messages are all closed before any
     * of their arms closes its own.
     */
    private boolean closeMessages(int ordinal, String guard, String owner,
                                  List<AttachRow> attaches,
                                  Set<String> reached, List<String> stated,
                                  List<GapRow> refusals, int depth) {
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
            if (attach.interaction() == null) {
                // No producer, so no family: a free constant, refused.
                refusals.add(GapRow.of(owner, GapKind.UNATTESTED_ARM,
                        GapClass.DIAGNOSTIC, attach.symbol(), "a delivery "
                                + "this rests on was handed a value its "
                                + "attach pairs with no producer, so "
                                + "nothing binds it"));
                return false;
            }
            if (!seen.add(attach.endpoint().id())) continue;
            String correlation = attach.correlationId();
            add(byMessage, correlation == null || correlation.isEmpty()
                    ? "@" + attach.endpoint().id() : correlation, attach);
        }
        Map<String, Closed> opened = new LinkedHashMap<String, Closed>();
        for (Map.Entry<String, List<AttachRow>> message
                : byMessage.entrySet()) {
            String group = groupId(message.getValue());
            Closed held = closed.get(group);
            if (held == null) {
                held = new Closed("message_family__" + ordinal + "__"
                        + ArtifactIO.digest(group, 12), guard.equals(path));
                closed.put(group, held);
                pathUndo.add(() -> closed.remove(group));
                opened.put(message.getKey(), held);
            }
            needs(held, guard);
        }
        for (Map.Entry<String, List<AttachRow>> message
                : byMessage.entrySet()) {
            Closed family = opened.get(message.getKey());
            if (family == null) continue;
            List<AttachRow> leaves = message.getValue();
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
            // One message not closed refuses what rests on it, and the
            // rollback of that takes the message back.
            if (eligible == null || !messageFamily(ordinal, family, owner,
                    message.getKey(), leaves, slotOf, symbolOf, eligible,
                    attestedAt, bySession, reached, stated, refusals,
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
     * and the model names which RUN's response the witness rests on, under
     * what rests on the message ({@link Closed}).
     */
    private boolean messageFamily(
            int ordinal, Closed family, String owner, String message,
            List<AttachRow> leaves, Map<String, Interaction> slotOf,
            Map<String, String> symbolOf, List<String> eligible,
            Map<String, Set<String>> attestedAt,
            Map<String, List<Arms.Arm>> bySession, Set<String> reached,
            List<String> stated, List<GapRow> refusals, int depth) {
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
            // Declared BEFORE the body, whose nested families name it.
            lowering.declare(selector, VmTermLowering.Sort.BOOL);
            List<String> nested = new ArrayList<String>();
            Map<String, BoundHole> holes =
                    new LinkedHashMap<String, BoundHole>();
            int[] mark = mark();
            String body = producerBody(ordinal, selector, message, session,
                    bindings(held), reached, nested, depth, holes);
            String same = body == null ? null : selectorOf.get(body);
            // A refused arm, or a copy of one taken already (which rests on
            // the same nested messages), states nothing.
            if (body == null || same != null) rollback(mark);
            if (body == null) continue;
            if (same != null) {
                choose(same, armChoices.get(same).alsoBy(session));
                continue;
            }
            stated.addAll(nested);
            selectorOf.put(body, selector);
            representatives.add(session);
            selectors.add(selector);
            cases.add("(=> " + selector + " " + body + ")");
            choose(selector, ArmChoice.of(family.name, group,
                    endpointIds(leaves), session, held, holes));
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
            family(slot.getKey(), Family.of(slot.getKey(), rows));
        }
        cases.add(0, Arms.exactlyOne(selectors));
        family.formula = VmTermLowering.and(cases);
        family.selectors = selectors;
        stated.add(family.formula);
        // A message an arm rests on is asserted once the path's arms are
        // all known (commit).
        if (family.atPath) {
            assertFamily(family.name, "(=> " + path + " " + family.formula
                    + ")");
        }
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
        Set<String> own = flips(owner);
        List<String> arms = new ArrayList<String>();
        for (String session : eligible) {
            Set<String> producer = flips(session);
            if (own.containsAll(producer) || producer.containsAll(own)) {
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
     * ONE HOLE'S ARM (WIRE-CODEC §6.1, §6.3): the hole's symbol, declared at
     * the decoded leaf's sort, bound to the operand the producer's export
     * cut out of its leaf by the one hole-arm rule
     * ({@link VmTermLowering#holeArm}); a relay's operand is the upstream
     * hole's symbol, closed below as a nested family.  What the value rests
     * on is noted for CONFIRM ({@link BoundHole}).
     *
     * @return the binding, or null with the refusal in {@code refused}
     */
    private String hole(String session, Arms.Arm arm, Term delivered,
                        Map<String, BoundHole> holes, List<GapRow> refused) {
        AttachRow consumer = arm.attach();
        VmTermLowering.HoleArm bound = VmTermLowering.holeArm(arm.symbol(),
                delivered, arm.export().javaType(), consumer.javaType());
        if (bound.refusal != null) {
            refused.add(GapRow.of(session, bound.refusal,
                    GapClass.DIAGNOSTIC, arm.slotId(), bound.detail));
            return null;
        }
        lowering.declareStated(arm.symbol(),
                JavaSmtSorts.sortOfJava(consumer.javaType()));
        boolean clocked = false;
        Set<String> nested = new LinkedHashSet<String>();
        for (String name : lowering.reachedSymbols(
                Collections.singletonList(delivered.text))) {
            RootMintRow root = corpus.rootBySymbol(session, name);
            clocked |= root != null && root.kind() == RootKind.CLOCK;
            if (!name.equals(arm.symbol())
                    && corpus.attach(session, name) != null) {
                nested.add(name);
            }
        }
        holes.put(consumer.endpoint().id(),
                new BoundHole(arm.symbol(), consumer.javaType(), clocked,
                        nested));
        return bound.formula;
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
     * @param selector this arm's selector, which (iv)'s families rest on
     * @param holes receives the codec holes the outs bind, by consumer
     *              endpoint id ({@link ArmChoice#holes})
     * @return the arm-set's conjunction, or null when a value it rests on is
     *         not stated -- refusing this {@code (P, S)}, not the path
     */
    private String producerBody(int ordinal, String selector,
                                String subject,
                                String session,
                                List<Out> outs, Set<String> reachedSlots,
                                List<String> nestedStated, int depth,
                                Map<String, BoundHole> holes) {
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
            if (out.arm.hole()) {
                String bound = hole(session, out.arm, delivered, holes,
                        local);
                if (bound == null) {
                    stated = false;
                    break;
                }
                conjuncts.add(bound);
                guards.putAll(out.arm.guard());
                continue;
            }
            for (String symbol : out.symbols) {
                if (symbol == null || symbol.isEmpty()) continue;
                lowering.declareStated(symbol, delivered.sort);
                conjuncts.add("(= " + symbol + " " + delivered.text + ")");
                // The states of the stored object the reader could have
                // seen through this very store.
                if (out.arm.write() != null) {
                    conjuncts.add(lowering.storeChoice(symbol,
                            out.arm.write()));
                }
            }
            guards.putAll(out.arm.guard());
        }
        // The delivering replay's valuation of every varied root.
        for (Map.Entry<String, String> guard : guards.entrySet()) {
            // The guard's root must be declared: an arm need not mention
            // it, and an undeclared constant makes z3 answer with an error.
            VmTermLowering.Sort sort = lowering.statedSort(guard.getKey());
            if (sort == null) {
                composer.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        guard.getKey(), "an arm of " + subject
                                + " is guarded by a symbol no row of this "
                                + "corpus declares a sort for");
                continue;
            }
            String literal = smtLiteral(guard.getValue(), sort);
            if (literal.isEmpty()) continue;
            lowering.declareStated(guard.getKey());
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
            composer.frameRefusals(session, reached.keySet(), local);
            // What the delivered values, the decisions a delivered referent
            // was built under, and the handoffs a nested family binds rest
            // on (Independence).
            List<String> delivered = new ArrayList<String>();
            for (Out out : outs) {
                delivered.add(out.arm.expressionRef());
                for (DecisionRow built : composer.constructionGuards(session,
                        out.arm.write())) {
                    delivered.add(Arms.conjunct(built));
                }
            }
            Set<String> bound = new LinkedHashSet<String>();
            for (Out out : outs) {
                for (String symbol : out.arm.nested()) {
                    if (corpus.attach(session, symbol) != null) {
                        bound.add(symbol);
                    }
                }
            }
            Independence relevant = composer.independence(session,
                    delivered, bound, reached,
                    composer.reachedConditions(session, reached));
            Set<String> answered = new LinkedHashSet<String>();
            composer.statedReads(session, reached.keySet(), relevant, rows,
                    local, joins, answered);
            composer.stateJoins(session, reached.keySet(), relevant, rows,
                    local, new ArrayList<ReadRow>(), joins, answered);
            conjuncts.addAll(composer.closureConditions(session, reached,
                    relevant, local));
            Set<String> held = new LinkedHashSet<String>();
            for (Out out : outs) {
                if (out.arm.write() == null) continue;
                for (String symbol : out.symbols) {
                    for (SmtLowering.StateChoice state : lowering
                            .stateChoices(session, symbol, out.arm.write())) {
                        if (!held.add(state.selector)) continue;
                        conjuncts.add(stateClosure(session, out, state,
                                reached, bound, rows, joins, answered));
                    }
                }
            }
            // Nested families rest on THIS ARM's selector: what the run
            // delivering it was handed holds when the witness takes it.
            List<String> asks = new ArrayList<String>(conjuncts);
            asks.addAll(composer.statedJoins(joins,
                    Collections.<String>emptySet(), conjuncts,
                    Collections.<String>emptyList()));
            stated = closeMessages(ordinal, selector, session,
                    handedOn(session, outs, asks, local), reachedSlots,
                    nested, local, depth + 1);
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

    /**
     * A STATE OF A DELIVERED OBJECT RESTS ON WHAT MADE IT, as the store
     * rests on its own prefix: a later version a query through the read may
     * see ({@link SmtLowering#stateChoices}) was written by an occurrence the
     * arm's closure need not reach, under decisions of its own.  Under that
     * state's selector, the closure its write adds to the store producer's
     * ({@link Composer#closure} seeded with it; EXPLORE demands the same
     * writers, {@code Corpus#referentStates}): each added occurrence's
     * decisions before its cutoff, and the reads they rest on joined.  A
     * state whose added closure the recording does not state is no option
     * of the arm, refused by name.
     *
     * @return the state's conjunct, or "" when its write adds no decision
     */
    private String stateClosure(String session, Out out,
                                SmtLowering.StateChoice state,
                                Map<String, Long> reached, Set<String> bound,
                                SmtLowering.SessionJoin rows,
                                Map<String, String> joins,
                                Set<String> answered) {
        Map<String, Long> added = new LinkedHashMap<String, Long>();
        for (Map.Entry<String, Long> at : composer.closure(session,
                out.arm.producer(), out.arm.deliveredAt(),
                Collections.singletonList(state.state)).entrySet()) {
            Long was = reached.get(at.getKey());
            if (was == null || was.longValue() < at.getValue().longValue()) {
                added.put(at.getKey(), at.getValue());
            }
        }
        if (added.isEmpty()) return "";
        List<GapRow> refused = new ArrayList<GapRow>();
        composer.frameRefusals(session, added.keySet(), refused);
        Independence relevant = composer.independence(session,
                Collections.singletonList(state.state.expressionRef()), bound,
                added, composer.reachedConditions(session, added));
        composer.statedReads(session, added.keySet(), relevant, rows,
                refused, joins, answered);
        composer.stateJoins(session, added.keySet(), relevant, rows, refused,
                new ArrayList<ReadRow>(), joins, answered);
        List<String> conditions = composer.closureConditions(session, added,
                relevant, refused);
        if (refused.isEmpty()) {
            String held = VmTermLowering.and(conditions);
            return "true".equals(held) ? ""
                    : "(=> " + state.selector + " " + held + ")";
        }
        for (GapRow gap : refused) {
            gaps.add(GapRow.of(gap.sessionId(), gap.kind(), GapClass.DIAGNOSTIC,
                    gap.subject(), "state " + SmtLowering.locationKey(
                            state.state.location()) + "@"
                            + state.state.version() + " (" + state.selector
                            + ") is no option: its writer's closure "
                            + gap.detail()));
        }
        return "(not " + state.selector + ")";
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
     * closure, above): every handoff variable the arm's conjunction names
     * but the leaves it binds -- its delivered expressions'
     * ({@link Arms.Arm#nested}) and those its closure's conditions and
     * joins read (hdfs-11741 r8: the balancer's block-key expiry, joined in
     * a move task's closure) -- resolved in the delivering session.  Unbound,
     * each would be a free constant inside the arm; one that session
     * minted no attach for has no family there, and refuses the arm.
     */
    private List<AttachRow> handedOn(String session, List<Out> outs,
                                     List<String> asks,
                                     List<GapRow> refused) {
        Set<String> names = new LinkedHashSet<String>();
        Set<String> leaves = new LinkedHashSet<String>();
        for (Out out : outs) {
            names.addAll(out.arm.nested());
            leaves.addAll(out.symbols);
        }
        names.addAll(lowering.reachedSymbols(asks));
        names.removeAll(leaves);
        List<AttachRow> attaches = new ArrayList<AttachRow>();
        for (String name : names) {
            AttachRow attach = corpus.attach(session, name);
            if (attach != null) {
                attaches.add(attach);
            } else if (corpus.handoffSymbol(name)) {
                refused.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.DIAGNOSTIC, name, "an arm names a handoff "
                                + "variable no attach row of its session "
                                + "minted, so no family of that run binds "
                                + "it"));
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
     * is ruled out ({@link ClaimPolicy}).  A writer arm's delivery rests on
     * the messages it was handed as a message arm's does
     * ({@link #closeMessages}).
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
            // Every writer named: no read met a writer the log never named.
            boolean named = true;
            for (ReadRow read : reads) named &= !read.unnamedWriter();
            for (Arms.Arm arm : arms.stateArms(reads.get(0).endpoint(),
                    session, entry.getKey(),
                    reads.get(0).observedVersion(), named)) {
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
                family(arm.slotId(), Family.of(arm.slotId(),
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
            // One arm is the run's own interleaving: the join says it.  An
            // alternative is an HB-concurrent writer: arms that are each the
            // run's own pairing of some read (the writer one read saw, the
            // pins of another whose version no row wrote) re-pair nothing,
            // and their location is none Composer#repaired names.
            boolean alternative = false;
            for (Arms.Arm arm : found) {
                alternative |= arms.concurrent(reads.get(0).endpoint()
                        .occurrence(), arm.producer(), session);
            }
            if (!alternative
                    || found.size() + (observedPin.isEmpty() ? 0 : 1) < 2) {
                continue;
            }
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
        // Nested selector -> the arms delivering a store it is a state of.
        Map<String, List<String>> delivering =
                new LinkedHashMap<String, List<String>>();
        for (Map.Entry<String, List<Out>> writer
                : outsOfWriter.entrySet()) {
            String name = "writer_arm__" + ordinal + "__"
                    + ArtifactIO.digest(writer.getKey() + "|" + session, 12);
            lowering.declare(name, VmTermLowering.Sort.BOOL);
            int[] mark = mark();
            String body = producerBody(ordinal, name, writer.getKey(),
                    session, writer.getValue(), reached,
                    new ArrayList<String>(), 0,
                    new LinkedHashMap<String, BoundHole>());
            if (body == null) {
                rollback(mark);
                continue;
            }
            selectorOf.put(writer.getKey(), name);
            String assertion = "writer_family__" + ordinal + "__"
                    + ArtifactIO.digest(writer.getKey() + "|" + session, 12);
            String formula = "(=> " + name + " " + body + ")";
            stated.add(formula);
            assertFamily(assertion,
                    "(=> " + selector + " " + formula + ")");
            List<SmtLowering.StateChoice> states =
                    new ArrayList<SmtLowering.StateChoice>();
            for (Out out : writer.getValue()) {
                if (out.arm.write() == null) continue;
                for (String symbol : out.symbols) {
                    for (SmtLowering.StateChoice state : lowering
                            .stateChoices(session, symbol, out.arm.write())) {
                        states.add(state);
                        add(delivering, state.selector, name);
                    }
                }
            }
            choose(name, ArmChoice.of(assertion,
                    writer.getKey(), Collections.<String>emptyList(),
                    session, armsOf(writer.getValue()),
                    Collections.<String, BoundHole>emptyMap()).seeing(states));
        }
        // Every nested selector this path minted holds only under an arm
        // of it delivering a store its state was seen through: under none
        // -- the arm of the store the read observed, the pins', no family,
        // a selector of another session's scope -- the run's own object
        // answers as the run saw it ({@code SmtLowering#answerOf}).
        for (String nested : lowering.nestedSelectors()) {
            List<String> by = delivering.get(nested);
            String formula = "(=> " + nested + " " + VmTermLowering.or(
                    by == null ? Collections.<String>emptyList() : by) + ")";
            stated.add(formula);
            assertFamily("nest_family__" + ordinal + "__"
                            + ArtifactIO.digest(nested + "|" + session, 12),
                    "(=> " + selector + " " + formula + ")");
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
                assertFamily(assertion,
                        "(=> " + selector + " " + formula + ")");
                choose(name, ArmChoice.of(assertion,
                        "observed:" + location.getKey(),
                        Collections.<String>emptyList(), session,
                        Collections.<Arms.Arm>emptyList(),
                        Collections.<String, BoundHole>emptyMap()));
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
            assertFamily("state_family__" + ordinal + "__"
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
        // A row that states no expression delivered a value the VM did not
        // follow: no arm rests on it (Arms#arm), and it cites nothing the
        // table could lack (hdfs-11741 r4: the second move task's export).
        if (reader == null || expressionRef == null
                || expressionRef.isEmpty()) {
            return null;
        }
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
