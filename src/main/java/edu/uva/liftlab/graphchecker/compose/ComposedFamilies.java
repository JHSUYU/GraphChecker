package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.Flip;
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
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.explore.Corpus;
import edu.uva.liftlab.graphchecker.runtime.Confirmation;
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

final class ComposedFamilies {

    private final Composer composer;
    private final Corpus corpus;
    private final Arms arms;
    private final SmtLowering lowering;
    private final Map<String, Family> families;
    private final Map<String, Set<String>> unattestedRoots;
    private final Set<String> replacing;
    private final List<GapRow> gaps;
    private final Set<String> slotNamed = new LinkedHashSet<String>();
    private final Set<String> unpairedNamed = new LinkedHashSet<String>();
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
        private final Map<String, BoundLeaf> leaves;

        private ArmChoice(String family, String groupId,
                          List<String> attachEndpointIds,
                          List<String> sessionIds, String producerPathId,
                          List<String> interactionIds,
                          List<String> expressionRefs, boolean attested,
                          List<SmtLowering.StateChoice> states,
                          Map<String, BoundLeaf> leaves) {
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
            this.leaves = Collections.unmodifiableMap(leaves);
        }

        static ArmChoice of(String family, String groupId,
                            List<String> attachEndpointIds, String session,
                            List<Arms.Arm> arms, Map<String, BoundLeaf> leaves) {
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
                    Collections.<SmtLowering.StateChoice>emptyList(), leaves);
        }

        ArmChoice alsoBy(String session) {
            List<String> sessions = new ArrayList<String>(sessionIds);
            sessions.add(session);
            return new ArmChoice(family, groupId, attachEndpointIds,
                    sessions, producerPathId, interactionIds,
                    expressionRefs, attested, states, leaves);
        }

        ArmChoice seeing(List<SmtLowering.StateChoice> seen) {
            return new ArmChoice(family, groupId, attachEndpointIds,
                    sessionIds, producerPathId, interactionIds,
                    expressionRefs, attested, seen, leaves);
        }

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

        public String family() {
            return family;
        }

        public String groupId() {
            return groupId;
        }

        public List<String> attachEndpointIds() {
            return attachEndpointIds;
        }

        public String sessionId() {
            return sessionIds.get(0);
        }

        public List<String> sessionIds() {
            return sessionIds;
        }

        public String producerPathId() {
            return producerPathId;
        }

        public List<String> interactionIds() {
            return interactionIds;
        }

        public List<String> expressionRefs() {
            return expressionRefs;
        }

        public boolean attested() {
            return attested;
        }

        public List<SmtLowering.StateChoice> states() {
            return states;
        }

        public Map<String, BoundLeaf> leaves() {
            return leaves;
        }
    }

    public static final class BoundLeaf {
        public final String symbol;
        public final String javaType;
        public final String occurrenceId;
        public final boolean clocked;
        public final Set<String> nested;
        public final Set<String> roots;

        BoundLeaf(String symbol, String javaType, String occurrenceId,
                  boolean clocked, Set<String> nested, Set<String> roots) {
            this.symbol = symbol;
            this.javaType = javaType;
            this.occurrenceId = occurrenceId;
            this.clocked = clocked;
            this.nested = Collections.unmodifiableSet(nested);
            this.roots = Collections.unmodifiableSet(roots);
        }

        public boolean held(String anchorId) {
            return occurrenceId.equals(anchorId);
        }
    }

    public static Map<String, String> texts(Collection<ArmChoice> selected,
                                            Map<String, String> model,
                                            String anchorId,
                                            Collection<String> moved) {
        Map<String, BoundLeaf> bySymbol =
                new LinkedHashMap<String, BoundLeaf>();
        Map<String, String> consumerOf = new LinkedHashMap<String, String>();
        for (ArmChoice arm : selected) {
            for (Map.Entry<String, BoundLeaf> leaf
                    : arm.leaves().entrySet()) {
                bySymbol.put(leaf.getValue().symbol, leaf.getValue());
                consumerOf.put(leaf.getValue().symbol, leaf.getKey());
            }
        }
        Map<String, String> texts = new LinkedHashMap<String, String>();
        for (Map.Entry<String, BoundLeaf> leaf : bySymbol.entrySet()) {
            if (!leaf.getValue().held(anchorId)
                    || clocked(leaf.getKey(), bySymbol,
                    new LinkedHashSet<String>())
                    || !moves(leaf.getKey(), bySymbol, moved,
                    new LinkedHashSet<String>())) {
                continue;
            }
            String value = model.get(leaf.getKey());
            String text = value == null ? null
                    : text(leaf.getValue().javaType, value);
            if (text != null) {
                texts.put(consumerOf.get(leaf.getKey()), text);
            }
        }
        return texts;
    }

    private static String text(String javaType, String value) {
        VmTermLowering.Sort sort = JavaSmtSorts.sortOfJava(javaType);
        if (sort == VmTermLowering.Sort.STRING) return Z3.javaString(value);
        return sort == VmTermLowering.Sort.BOOL
                || sort == VmTermLowering.Sort.INT && !"C".equals(javaType)
                ? value : null;
    }

    private static boolean moves(String symbol,
                                 Map<String, BoundLeaf> bySymbol,
                                 Collection<String> moved, Set<String> seen) {
        BoundLeaf leaf = bySymbol.get(symbol);
        if (leaf == null || !seen.add(symbol)) return false;
        for (String root : leaf.roots) {
            if (moved.contains(root)) return true;
        }
        for (String nested : leaf.nested) {
            if (moves(nested, bySymbol, moved, seen)) return true;
        }
        return false;
    }

    private static boolean clocked(String symbol,
                                   Map<String, BoundLeaf> bySymbol,
                                   Set<String> seen) {
        BoundLeaf leaf = bySymbol.get(symbol);
        if (leaf == null || !seen.add(symbol)) return true;
        if (leaf.clocked) return true;
        for (String nested : leaf.nested) {
            if (clocked(nested, bySymbol, seen)) return true;
        }
        return false;
    }

    private final Map<String, ArmChoice> armChoices =
            new LinkedHashMap<String, ArmChoice>();

    Map<String, ArmChoice> armChoices() {
        return Collections.unmodifiableMap(armChoices);
    }

    private final List<String> pathAssertions = new ArrayList<String>();
    private final List<Runnable> pathUndo = new ArrayList<Runnable>();
    private String path;
    private String pathSession;
    private final Map<String, Closed> closed =
            new LinkedHashMap<String, Closed>();

    private static final class Closed {
        final String name;
        final boolean atPath;
        final List<String> needers = new ArrayList<String>();
        String formula;
        List<String> selectors;

        Closed(String name, boolean atPath) {
            this.name = name;
            this.atPath = atPath;
        }
    }

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
        pathSession = null;
    }

    void discard() {
        rollback(new int[]{0, 0, lowering.unboundMark()});
        path = null;
        pathSession = null;
    }

    private int[] mark() {
        return new int[]{pathAssertions.size(), pathUndo.size(),
                lowering.unboundMark()};
    }

    private void rollback(int[] mark) {
        lowering.unboundRollback(mark[2]);
        List<String> assertions =
                pathAssertions.subList(mark[0], pathAssertions.size());
        lowering.retract(assertions);
        assertions.clear();
        List<Runnable> undo = pathUndo.subList(mark[1], pathUndo.size());
        for (int at = undo.size() - 1; at >= 0; at--) undo.get(at).run();
        undo.clear();
    }

    private void assertFamily(String name, String formula) {
        lowering.assertNamed(name, formula);
        pathAssertions.add(name);
    }

    private void choose(String selector, ArmChoice choice) {
        ArmChoice before = armChoices.put(selector, choice);
        pathUndo.add(() -> restore(armChoices, selector, before));
    }

    private void family(String slotId, Family family) {
        Family before = families.put(slotId, family);
        pathUndo.add(() -> restore(families, slotId, before));
    }

    private final Map<String, List<String>> ownArms =
            new LinkedHashMap<String, List<String>>();

    Map<String, List<String>> ownArms() {
        return Collections.unmodifiableMap(ownArms);
    }

    private void own(String arm) {
        own(ownArms, arm);
    }

    private final Map<String, List<String>> recordedAtPlants =
            new LinkedHashMap<String, List<String>>();

    Map<String, List<String>> recordedAtPlants() {
        return Collections.unmodifiableMap(recordedAtPlants);
    }

    private final Map<String, Map<String, List<String>>> worldArms =
            new LinkedHashMap<String, Map<String, List<String>>>();

    Map<String, Map<String, List<String>>> worldArms() {
        return Collections.unmodifiableMap(worldArms);
    }

    private void own(Map<String, List<String>> owned, String arm) {
        List<String> arms = owned.computeIfAbsent(path,
                key -> new ArrayList<String>());
        arms.add(arm);
        pathUndo.add(() -> arms.remove(arms.size() - 1));
    }

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

    boolean closeFamilies(int ordinal, String selector, String session,
                          Set<String> reached,
                          List<AttachRow> bound, List<String> stated,
                          List<GapRow> refusals) {
        path = selector;
        pathSession = session;
        return closeMessages(ordinal, selector, bound, reached, stated,
                refusals, 0);
    }

    List<String> closeViewVersions(int ordinal,
                                   Map<String, List<AttachRow>> byGuard,
                                   Set<String> reached,
                                   List<String> stated) {
        List<String> unpaired = new ArrayList<String>();
        for (Map.Entry<String, List<AttachRow>> version
                : byGuard.entrySet()) {
            int[] mark = mark();
            Set<String> slots = new LinkedHashSet<String>(reached);
            List<String> said = new ArrayList<String>();
            List<GapRow> refusals = new ArrayList<GapRow>();
            if (closeMessages(ordinal, version.getKey(), version.getValue(),
                    slots, said, refusals, 0)) {
                reached.addAll(slots);
                stated.addAll(said);
                continue;
            }
            rollback(mark);
            unpaired.add(version.getKey());
            composer.gap(GapKind.UNPRODUCIBLE_ANSWER, GapClass.DIAGNOSTIC,
                    lowering.viewGuardName(version.getKey()), "no session"
                            + " of this corpus can send what the view holds"
                            + " at this version, so the read is not paired"
                            + " to it: the path holds its version choice"
                            + " false" + (refusals.isEmpty() ? ""
                            : " (" + refusals.get(0).subject() + ": "
                            + refusals.get(0).detail() + ")"));
        }
        return unpaired;
    }

    private static final int NESTING_LIMIT = 16;

    private boolean closeMessages(int ordinal, String guard,
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
        Map<String, List<AttachRow>> byMessage =
                new LinkedHashMap<String, List<AttachRow>>();
        Set<String> seen = new LinkedHashSet<String>();
        for (AttachRow attach : attaches) {
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
            Map<String, Interaction> slotOf =
                    new LinkedHashMap<String, Interaction>();
            Map<String, String> symbolOf =
                    new LinkedHashMap<String, String>();
            Map<String, List<Arms.Arm>> bySession =
                    new LinkedHashMap<String, List<Arms.Arm>>();
            Map<String, Set<String>> attestedAt =
                    new LinkedHashMap<String, Set<String>>();
            Map<String, Endpoint> producerOf =
                    new LinkedHashMap<String, Endpoint>();
            for (AttachRow attach : leaves) {
                Interaction slot = attach.interaction();
                if (slotOf.containsKey(slot.id())) continue;
                slotOf.put(slot.id(), slot);
                symbolOf.put(slot.id(), attach.symbol());
                producerOf.put(slot.id(), attach.producer());
                attestedAt.put(slot.id(), new LinkedHashSet<String>());
                for (Arms.Arm arm : arms.armsAt(slot, attach.symbol(),
                        attach.sessionId())) {
                    if (replacing.contains(arm.sessionId())) continue;
                    if (arm.producer() == null || leftPath(arm)) continue;
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
            int before = refusals.size();
            List<String> eligible = eligibleSessions(message.getKey(),
                    slotOf.keySet(), attestedAt, producerOf, refusals);
            if (eligible == null || !messageFamily(ordinal, family,
                    message.getKey(), leaves, slotOf, symbolOf, eligible,
                    attestedAt, bySession, reached, stated, refusals,
                    depth)) {
                if (!heldOwn(family, message.getKey(), leaves, bySession,
                        stated)) {
                    return false;
                }
                refusals.subList(before, refusals.size()).clear();
            }
        }
        return true;
    }

    private boolean heldOwn(Closed family, String message,
                            List<AttachRow> leaves,
                            Map<String, List<Arms.Arm>> bySession,
                            List<String> stated) {
        if (!family.atPath || bySession.containsKey(pathSession)) {
            return false;
        }
        List<String> holds = new ArrayList<String>();
        for (AttachRow leaf : leaves) {
            String hold = leaf.sessionId().equals(pathSession)
                    ? composer.arrivalEquation(leaf) : null;
            if (hold == null) return false;
            holds.add(hold);
        }
        for (AttachRow leaf : leaves) {
            composer.heldArrival(leaf, "message " + message + " is attested"
                    + " by no run whose world is compatible with this path's,"
                    + " and this path's own run delivered it from a producer"
                    + " it ran uninstrumented");
        }
        family.formula = VmTermLowering.and(holds);
        family.selectors = Collections.<String>emptyList();
        stated.add(family.formula);
        assertFamily(family.name, "(=> " + path + " " + family.formula + ")");
        return true;
    }

    private final Set<String> leftNamed = new LinkedHashSet<String>();
    private final Set<String> unheldNamed = new LinkedHashSet<String>();
    private String lastRefusal = "";

    private boolean leftPath(Arms.Arm arm) {
        String why = composer.leftPath(arm);
        if (why == null) return false;
        if (leftNamed.add(path + "|" + arm.slotId() + "|"
                + arm.sessionId())) {
            composer.gap(GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    arm.slotId() + " of " + arm.sessionId(), why);
        }
        return true;
    }

    private static String groupId(List<AttachRow> leaves) {
        List<String> ids = endpointIds(leaves);
        Collections.sort(ids);
        return String.join("|", ids);
    }

    private List<String> eligibleSessions(
            String message, Set<String> slots,
            Map<String, Set<String>> attestedAt,
            Map<String, Endpoint> producerOf, List<GapRow> refusals) {
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
                for (String leaf : slots) {
                    Set<String> attesting = attestedAt.get(leaf);
                    if (attesting == null || attesting.isEmpty()) {
                        nameTickBound(producerOf.get(leaf), message);
                    }
                }
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

    private final Set<String> tickNamed = new LinkedHashSet<String>();

    private void nameTickBound(Endpoint producer, String message) {
        if (producer == null) return;
        Corpus.TickPast tick = corpus.tickPastRecording(
                producer.occurrence());
        if (tick == null) return;
        String subject = producer.occurrence().render() + " "
                + Composer.DAEMON_TICK_BOUND + "=" + tick.last;
        if (!tickNamed.add(subject)) return;
        composer.gap(GapKind.BOUND_INSUFFICIENT, GapClass.DIAGNOSTIC, subject,
                "a message an arm was handed (" + message + ") holds a leaf"
                        + " this producer wrote, begun by the daemon tick "
                        + tick.tick + " past the recording's last: no session"
                        + " ran it instrumented, so the arm resting on that"
                        + " message is refused (UNPRODUCIBLE_ANSWER)");
    }

    private boolean messageFamily(
            int ordinal, Closed family, String message,
            List<AttachRow> leaves, Map<String, Interaction> slotOf,
            Map<String, String> symbolOf, List<String> eligible,
            Map<String, Set<String>> attestedAt,
            Map<String, List<Arms.Arm>> bySession, Set<String> reached,
            List<String> stated, List<GapRow> refusals, int depth) {
        String group = groupId(leaves);
        List<String> senders = compatible(eligible, bySession);
        if (senders.isEmpty()) {
            refusals.add(GapRow.of(pathSession, GapKind.UNPRODUCIBLE_ANSWER,
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
        Map<String, String> selectorOf = new LinkedHashMap<String, String>();
        List<String> representatives = new ArrayList<String>();
        for (String session : senders) {
            List<Arms.Arm> held = oneArmPerLeaf(bySession.get(session),
                    message, session);
            if (held == null || held.isEmpty()) continue;
            String selector = "message_arm__" + ordinal + "__"
                    + ArtifactIO.digest(group + "|" + session, 12);
            lowering.declare(selector, VmTermLowering.Sort.BOOL);
            List<String> nested = new ArrayList<String>();
            Map<String, BoundLeaf> bound =
                    new LinkedHashMap<String, BoundLeaf>();
            int[] mark = mark();
            String body = producerBody(ordinal, selector, message, session,
                    bindings(held), reached, nested, depth, bound);
            String same = body == null ? null : selectorOf.get(body);
            if (body == null || same != null) rollback(mark);
            if (body == null) continue;
            if (family.atPath && session.equals(pathSession)) {
                own(same != null ? same : selector);
            }
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
                    endpointIds(leaves), session, held, bound));
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
        if (family.atPath) {
            assertFamily(family.name, "(=> " + path + " " + family.formula
                    + ")");
        }
        return true;
    }

    private List<String> compatible(List<String> eligible,
                                    Map<String, List<Arms.Arm>> bySession) {
        Set<String> own = flips(pathSession);
        List<String> senders = new ArrayList<String>();
        for (String session : eligible) {
            Set<String> producer = flips(session);
            if ((own.containsAll(producer) || producer.containsAll(own))
                    && agrees(session, bySession.get(session))) {
                senders.add(session);
            }
        }
        return senders;
    }

    private Set<String> flips(String session) {
        Set<String> held = new LinkedHashSet<String>();
        for (Flip flip : corpus.world(session).flips) {
            held.add(flip.focusedOccurrenceId + "|" + flip.siteId + "#"
                    + flip.ordinal + "=" + flip.outcome);
        }
        return held;
    }

    private boolean agrees(String session, List<Arms.Arm> arms) {
        if (session.equals(pathSession) || arms == null || arms.isEmpty()) {
            return true;
        }
        return agreed.computeIfAbsent(pathSession + "|" + session, key -> {
            for (Arms.Arm arm : arms) {
                for (Map.Entry<String, RootMintRow> pinned
                        : arm.guardMints().entrySet()) {
                    String rootId = pinned.getValue().rootId();
                    if (corpus.ranRoot(rootId, pathSession) == null) continue;
                    String own = corpus.rootValue(pathSession, rootId);
                    if (!own.isEmpty() && !own.equals(
                            arm.guard().get(pinned.getKey()))) {
                        return false;
                    }
                }
            }
            return true;
        });
    }

    private final Map<String, Boolean> agreed =
            new LinkedHashMap<String, Boolean>();

    private static List<String> endpointIds(List<AttachRow> leaves) {
        List<String> ids = new ArrayList<String>();
        for (AttachRow attach : leaves) {
            if (!ids.contains(attach.endpoint().id())) {
                ids.add(attach.endpoint().id());
            }
        }
        return ids;
    }

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

    private static final class Out {
        private final Arms.Arm arm;
        private final List<String> symbols;

        private Out(Arms.Arm arm, List<String> symbols) {
            this.arm = arm;
            this.symbols = symbols;
        }
    }

    private static List<Out> bindings(List<Arms.Arm> group) {
        List<Out> outs = new ArrayList<Out>();
        for (Arms.Arm arm : group) {
            outs.add(new Out(arm, Collections.singletonList(arm.symbol())));
        }
        return outs;
    }

    private void bind(String session, Arms.Arm arm, Term delivered,
                      Map<String, BoundLeaf> bound) {
        AttachRow consumer = arm.attach();
        boolean clocked = false;
        Set<String> nested = new LinkedHashSet<String>();
        Set<String> roots = new LinkedHashSet<String>();
        for (String name : lowering.reachedSymbols(
                Collections.singletonList(delivered.text))) {
            RootMintRow root = corpus.rootBySymbol(session, name);
            clocked |= root != null && root.kind() == RootKind.CLOCK;
            if (root != null) roots.add(root.rootId());
            if (!name.equals(arm.symbol())
                    && corpus.attach(session, name) != null) {
                nested.add(name);
            }
        }
        bound.put(consumer.endpoint().id(), new BoundLeaf(arm.symbol(),
                consumer.javaType(), consumer.endpoint().occurrence().id(),
                clocked, nested, roots));
    }

    private String producerBody(int ordinal, String selector,
                                String subject,
                                String session,
                                List<Out> outs, Set<String> reachedSlots,
                                List<String> nestedStated, int depth,
                                Map<String, BoundLeaf> leaves) {
        ArmBody body = new ArmBody(session, selector);
        boolean stated = body.deliveries(outs, leaves);
        body.heldRoots();
        if (stated) {
            stated = body.closure(ordinal, selector, outs, reachedSlots,
                    depth);
        }
        return body.end(stated, subject, nestedStated);
    }

    private final class ArmBody {
        private final String session;
        private final SmtLowering.SessionJoin rows;
        private final List<GapRow> local = new ArrayList<GapRow>();
        private final List<String> conjuncts = new ArrayList<String>();
        private final Map<String, String> guards =
                new LinkedHashMap<String, String>();
        private final Map<String, RootMintRow> guardMints =
                new LinkedHashMap<String, RootMintRow>();
        private final List<String> nested = new ArrayList<String>();
        private final Map<String, String> joins =
                new LinkedHashMap<String, String>();

        ArmBody(String session, String selector) {
            this.session = session;
            this.rows = corpus.join(session);
            lowering.begin(session, rows, corpus.expressions(session));
            lowering.arm(selector);
        }

        boolean deliveries(List<Out> outs, Map<String, BoundLeaf> leaves) {
            for (Out out : outs) {
                Term delivered = lower(session, out.arm.expressionRef(),
                        "arm:" + out.arm.slotId(), conjuncts);
                if (delivered == null) return false;
                if (out.arm.attach() != null) {
                    bind(session, out.arm, delivered, leaves);
                }
                String sent = sentType(session, out.arm.expressionRef());
                for (String symbol : out.symbols) {
                    if (symbol == null || symbol.isEmpty()) continue;
                    String received = received(symbol, delivered, sent);
                    if (received == null) return false;
                    conjuncts.add(received);
                    if (out.arm.write() != null) {
                        conjuncts.add(lowering.storeChoice(symbol,
                                out.arm.write()));
                    }
                }
                guards.putAll(out.arm.guard());
                guardMints.putAll(out.arm.guardMints());
            }
            return true;
        }

        void heldRoots() {
            for (Map.Entry<String, String> guard : guards.entrySet()) {
                VmTermLowering.Sort sort = lowering.statedSort(
                        guard.getKey());
                if (sort == null) {
                    sort = Composer.sortOf(guardMints.get(guard.getKey()));
                    lowering.declareStated(guard.getKey(), sort);
                }
                String literal = smtLiteral(guard.getValue(), sort);
                if (literal.isEmpty()) continue;
                lowering.declareStated(guard.getKey());
                conjuncts.add("(= " + guard.getKey() + " " + literal + ")");
            }
        }

        boolean closure(int ordinal, String selector, List<Out> outs,
                        Set<String> reachedSlots, int depth) {
            Map<String, Long> reached = producerClosure(session, outs);
            composer.frames(session, reached.keySet());
            List<String> delivered = new ArrayList<String>();
            for (Out out : outs) {
                delivered.add(out.arm.expressionRef());
                for (DecisionRow built : composer.restsOn
                        .constructionGuards(session, out.arm.write())) {
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
            Independence relevant = composer.restsOn.independence(session,
                    delivered, bound, reached,
                    composer.restsOn.reachedConditions(session, reached));
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
            List<String> asks = new ArrayList<String>(conjuncts);
            asks.addAll(composer.statedJoins(joins,
                    Collections.<String>emptySet(), conjuncts,
                    Collections.<String>emptyList()));
            List<String> holds = new ArrayList<String>();
            List<AttachRow> handed = handedOn(session, selector, outs, asks,
                    holds, local);
            conjuncts.addAll(holds);
            return closeMessages(ordinal, selector, handed, reachedSlots,
                    nested, local, depth + 1);
        }

        String end(boolean stated, String subject,
                   List<String> nestedStated) {
            List<String> reachTexts = new ArrayList<String>(conjuncts);
            reachTexts.addAll(nested);
            conjuncts.addAll(composer.statedJoins(joins,
                    Collections.<String>emptySet(), reachTexts,
                    Collections.<String>emptyList()));
            List<String> refused = new ArrayList<String>(
                    lowering.openRefusals());
            conjuncts.addAll(lowering.end());
            if (stated) {
                composer.unplacedClocks(session, conjuncts, joins, local);
            }
            if (!stated || !local.isEmpty() || !refused.isEmpty()) {
                lastRefusal = !local.isEmpty() ? local.get(0).kind() + " "
                        + local.get(0).subject() + ": "
                        + local.get(0).detail() : !refused.isEmpty()
                        ? "a value the recording does not state: "
                        + refused.get(0) : "a value it delivered does not"
                        + " lower";
                gaps.addAll(local);
                for (String refusal : refused) {
                    composer.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                            refusal, "the closure of " + subject
                                    + " in session " + session + " rests on "
                                    + "a value the recording does not state, "
                                    + "so that run is not one of its "
                                    + "options");
                }
                return null;
            }
            nestedStated.addAll(nested);
            return VmTermLowering.and(conjuncts);
        }
    }

    private Map<String, Long> producerClosure(String session, List<Out> outs) {
        Map<String, Long> reached = new LinkedHashMap<String, Long>();
        for (Map.Entry<String, List<Out>> each
                : byProducer(outs).entrySet()) {
            List<Out> its = each.getValue();
            long cutoff = Long.MIN_VALUE;
            for (Out out : its) {
                cutoff = Math.max(cutoff, out.arm.deliveredAt());
            }
            List<String> delivered = new ArrayList<String>();
            for (Out out : its) delivered.add(out.arm.expressionRef());
            Map<String, Long> one = composer.restsOn.closure(session,
                    its.get(0).arm.producer(), cutoff,
                    composer.restsOn.seedWrites(session, delivered));
            for (Map.Entry<String, Long> at : one.entrySet()) {
                Long was = reached.get(at.getKey());
                if (was == null
                        || was.longValue() < at.getValue().longValue()) {
                    reached.put(at.getKey(), at.getValue());
                }
            }
        }
        return reached;
    }

    private String stateClosure(String session, Out out,
                                SmtLowering.StateChoice state,
                                Map<String, Long> reached, Set<String> bound,
                                SmtLowering.SessionJoin rows,
                                Map<String, String> joins,
                                Set<String> answered) {
        Map<String, Long> added = new LinkedHashMap<String, Long>();
        for (Map.Entry<String, Long> at : composer.restsOn.closure(session,
                out.arm.producer(), out.arm.deliveredAt(),
                Collections.singletonList(state.state)).entrySet()) {
            Long was = reached.get(at.getKey());
            if (was == null || was.longValue() < at.getValue().longValue()) {
                added.put(at.getKey(), at.getValue());
            }
        }
        if (added.isEmpty()) return "";
        List<GapRow> refused = new ArrayList<GapRow>();
        composer.frames(session, added.keySet());
        Independence relevant = composer.restsOn.independence(session,
                Collections.singletonList(state.state.expressionRef()), bound,
                added, composer.restsOn.reachedConditions(session,
                        added));
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

    private static Map<String, List<Out>> byProducer(List<Out> outs) {
        Map<String, List<Out>> held =
                new LinkedHashMap<String, List<Out>>();
        for (Out out : outs) {
            add(held, out.arm.producer().id(), out);
        }
        return held;
    }

    private List<AttachRow> handedOn(String session, String selector,
                                     List<Out> outs, List<String> asks,
                                     List<String> holds,
                                     List<GapRow> refused) {
        Set<String> names = new LinkedHashSet<String>();
        Set<String> leaves = new LinkedHashSet<String>();
        for (Out out : outs) {
            names.addAll(out.arm.nested());
            leaves.addAll(out.symbols);
        }
        names.addAll(lowering.reachedSymbols(asks));
        List<AttachRow> attaches = new ArrayList<AttachRow>();
        composer.reachedHandoffs(session, names, leaves, holds, attaches,
                refused, selector);
        return attaches;
    }

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

    private static Arm row(Arms.Arm arm) {
        return Arm.of(arm.producerPathId().isEmpty() ? arm.sessionId()
                        : arm.producerPathId(), arm.producerPathId(),
                arm.expressionRef(), arm.guardRoots(), arm.attested());
    }

    private void slotOpened(String slotId, Interaction slot) {
        if (!composer.unopened(slot.consumer().id())) return;
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

    Set<String> stateFamilies(Corpus.RecordedPath path,
                              int ordinal, String selector,
                              List<ReadRow> joined,
                              Map<String, String> pins,
                              Set<String> reached,
                              List<String> stated,
                              List<String> recorded,
                              Map<String, String> planted,
                              Map<String, List<ReadRow>> sharing) {
        StateFamilies families = new StateFamilies(path, ordinal, selector,
                pins, reached, stated, sharing);
        Map<String, List<ReadRow>> byLocation =
                new LinkedHashMap<String, List<ReadRow>>();
        for (ReadRow read : joined) {
            add(byLocation, SmtLowering.locationKey(read.location()), read);
        }
        for (Map.Entry<String, List<ReadRow>> location
                : byLocation.entrySet()) {
            families.classify(location.getKey(), location.getValue());
        }
        families.holdBrokenBlocks();
        families.writerSelectors();
        families.holdUnstatedRuns();
        families.gateNestedSelectors();
        return families.locationFamilies(recorded, planted);
    }

    private static final class StateLocation {
        final String key;
        final List<ReadRow> reads;
        final List<String> symbols;
        final List<String> writers = new ArrayList<String>();
        String runWriter;
        List<String> observedPin;
        String unoffered;

        StateLocation(String key, List<ReadRow> reads) {
            this.key = key;
            this.reads = reads;
            this.symbols = new ArrayList<String>();
            for (ReadRow read : reads) symbols.add(read.symbol());
        }
    }

    private final class StateFamilies {
        private final Corpus.RecordedPath path;
        private final String session;
        private final int ordinal;
        private final String selector;
        private final Map<String, String> pins;
        private final Set<String> reached;
        private final List<String> stated;
        private final Map<String, List<ReadRow>> sharing;
        private final Map<String, StateLocation> locations =
                new LinkedHashMap<String, StateLocation>();
        private final Map<String, List<Out>> outsOfWriter =
                new LinkedHashMap<String, List<Out>>();
        private final Map<String, Set<String>> blockOf =
                new LinkedHashMap<String, Set<String>>();
        private final Map<String, String> selectorOf =
                new LinkedHashMap<String, String>();
        private final Map<String, String> refusedBodies =
                new LinkedHashMap<String, String>();
        private final Map<String, List<String>> delivering =
                new LinkedHashMap<String, List<String>>();

        StateFamilies(Corpus.RecordedPath path, int ordinal, String selector,
                      Map<String, String> pins, Set<String> reached,
                      List<String> stated,
                      Map<String, List<ReadRow>> sharing) {
            this.path = path;
            this.session = path.sessionId;
            this.ordinal = ordinal;
            this.selector = selector;
            this.pins = pins;
            this.reached = reached;
            this.stated = stated;
            this.sharing = sharing;
        }

        private List<ReadRow> sharingSymbols(StateLocation location) {
            Set<ReadRow> reads = new LinkedHashSet<ReadRow>(location.reads);
            for (ReadRow read : location.reads) {
                reads.addAll(sharing.getOrDefault(read.symbol(),
                        Collections.<ReadRow>emptyList()));
            }
            return new ArrayList<ReadRow>(reads);
        }

        void classify(String key, List<ReadRow> reads) {
            if (!Arms.namedOwner(reads.get(0).location())) {
                if (aliasingNamed.add(key)) {
                    composer.gap(GapKind.DECLARATION_MISSING,
                            GapClass.DIAGNOSTIC, key, "the owner on this "
                                    + "location's rows is a class and not the "
                                    + "rid of one object, so it names every "
                                    + "instance of that class at once: this "
                                    + "read is delivered as its own run "
                                    + "delivered it and gets no alternative "
                                    + "writers");
                }
                return;
            }
            StateLocation location = new StateLocation(key, reads);
            boolean outside = false;
            Set<Long> versions = new LinkedHashSet<Long>();
            String seen = null;
            for (ReadRow read : reads) {
                versions.add(read.observedVersion());
                WriteRow write = corpus.writeOf(session, key,
                        read.observedVersion());
                if (write == null) {
                    outside = true;
                } else {
                    seen = writer(write);
                }
            }
            boolean asHappened = outside || versions.size() > 1;
            OccurrenceAddress reader = reads.get(0).endpoint().occurrence();
            List<Arms.Arm> found = writerArms(location);
            fileRefusals();
            boolean alternative = false;
            for (Arms.Arm arm : found) {
                alternative |= arms.concurrent(reader, arm.producer(),
                        session);
            }
            if (!alternative
                    || found.size() + (asHappened ? 1 : 0) < 2) {
                return;
            }
            if (asHappened) {
                location.observedPin = observedPin(location.symbols, pins);
            } else {
                location.runWriter = seen;
            }
            for (Arms.Arm arm : found) {
                String writer = writer(arm.write());
                if (!location.writers.contains(writer)) {
                    location.writers.add(writer);
                }
                add(outsOfWriter, writer, new Out(arm, location.symbols));
                blockOf.computeIfAbsent(writer,
                        held -> new LinkedHashSet<String>()).add(key);
            }
            locations.put(key, location);
        }

        private List<Arms.Arm> writerArms(StateLocation location) {
            List<Arms.Arm> found = new ArrayList<Arms.Arm>();
            ReadRow first = location.reads.get(0);
            boolean named = true;
            for (ReadRow read : location.reads) {
                named &= !read.unnamedWriter();
            }
            for (Arms.Arm arm : arms.stateArms(first.endpoint(), session,
                    location.key, first.observedVersion(),
                    named && heldView(first))) {
                String aside = replacing.contains(arm.sessionId())
                        ? "its session is replaced"
                        : arm.producer() == null ? "it names no producer"
                        : leftPath(arm) ? "it is the anchor's work past the"
                        + " path" : !seenByAll(sharingSymbols(location), session,
                        location.key, arm.write()) ? "not every read of the"
                        + " location could have seen it" : null;
                if (aside != null) {
                    if (arm.write() != null && arm.write().version()
                            == first.observedVersion()) {
                        location.unoffered = aside;
                    }
                    continue;
                }
                if (!arm.attested()) {
                    noteUnattested(arm, "the arm states what it wrote and "
                            + "not why, so no witness may move a root "
                            + "inside it");
                }
                reached.add(arm.slotId());
                family(arm.slotId(), Family.of(arm.slotId(),
                        Collections.singletonList(row(arm))));
                found.add(arm);
            }
            return found;
        }

        private boolean heldView(ReadRow read) {
            if (read.location() == null
                    || read.location().kind() != LocationKind.VIEW
                    || Confirmation.hookPublishes(read.location())) {
                return true;
            }
            String view = SmtLowering.locationKey(read.location());
            if (unheldNamed.add(view)) {
                composer.gap(GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC, view,
                        "no publication hook publishes " + read.location()
                                + " (its system states no PUBLISHED_VIEW of"
                                + " it), so no hold can defer it: its read"
                                + " stays at the version it observed, "
                                + read.observedVersion()
                                + ", no version choice");
            }
            return false;
        }

        void holdBrokenBlocks() {
            for (StateLocation location : locations.values()) {
                String writer = location.runWriter;
                if (writer == null) continue;
                for (String other : blockOf.getOrDefault(writer,
                        Collections.<String>emptySet())) {
                    if (writer.equals(locations.get(other).runWriter)) {
                        continue;
                    }
                    location.observedPin = observedPin(location.symbols,
                            pins);
                    location.runWriter = null;
                    break;
                }
            }
        }

        void writerSelectors() {
            for (Map.Entry<String, List<Out>> writer
                    : outsOfWriter.entrySet()) {
                String name = "writer_arm__" + ordinal + "__"
                        + ArtifactIO.digest(writer.getKey() + "|" + session,
                        12);
                lowering.declare(name, VmTermLowering.Sort.BOOL);
                int[] mark = mark();
                lastRefusal = "a value it delivered does not lower";
                String body = writer.getKey().startsWith(INITIAL)
                        ? initialBody(session, writer.getValue())
                        : producerBody(ordinal, name, writer.getKey(),
                        session, writer.getValue(), reached,
                        new ArrayList<String>(), 0,
                        new LinkedHashMap<String, BoundLeaf>());
                if (body == null) {
                    refusedBodies.put(writer.getKey(), lastRefusal);
                    rollback(mark);
                    continue;
                }
                selectorOf.put(writer.getKey(), name);
                String assertion = "writer_family__" + ordinal + "__"
                        + ArtifactIO.digest(writer.getKey() + "|" + session,
                        12);
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
                                .stateChoices(session, symbol,
                                        out.arm.write())) {
                            states.add(state);
                            add(delivering, state.selector, name);
                        }
                    }
                }
                choose(name, ArmChoice.of(assertion,
                        writer.getKey(), Collections.<String>emptyList(),
                        session, armsOf(writer.getValue()),
                        Collections.<String, BoundLeaf>emptyMap())
                        .seeing(states));
            }
        }

        void holdUnstatedRuns() {
            for (StateLocation location : locations.values()) {
                String writer = location.runWriter;
                if (writer == null || selectorOf.containsKey(writer)) {
                    continue;
                }
                String why = refusedBodies.containsKey(writer)
                        ? "its body was refused: " + refusedBodies.get(writer)
                        : "its write is no arm here: " + (location.unoffered
                        == null ? "no expression of its run states it, or"
                        + " it names a root its run did not mint"
                        : location.unoffered);
                gaps.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.DIAGNOSTIC, location.key, "path "
                                + path.pathId + " observed one write, by "
                                + writer + ", whose arm states nothing ("
                                + why + "): the location is held by its"
                                + " observed arm, each read at its own join"
                                + " or pin -- the run as it happened --"
                                + " beside its other writers' arms: the"
                                + " reads keep their joins, and that"
                                + " writer's closure and store-state choices"
                                + " are not offered here"));
                location.observedPin = observedPin(location.symbols, pins);
                location.runWriter = null;
            }
        }

        void gateNestedSelectors() {
            for (String nested : lowering.nestedSelectors()) {
                List<String> by = delivering.get(nested);
                String formula = "(=> " + nested + " " + VmTermLowering.or(
                        by == null ? Collections.<String>emptyList() : by)
                        + ")";
                stated.add(formula);
                assertFamily("nest_family__" + ordinal + "__"
                                + ArtifactIO.digest(nested + "|" + session,
                                12),
                        "(=> " + selector + " " + formula + ")");
            }
        }

        Set<String> locationFamilies(List<String> recorded,
                                     Map<String, String> planted) {
            Set<String> chosen = new LinkedHashSet<String>();
            for (StateLocation location : locations.values()) {
                List<String> selectors = new ArrayList<String>();
                for (String writer : location.writers) {
                    String name = selectorOf.get(writer);
                    if (name != null) selectors.add(name);
                }
                if (selectors.size()
                        + (location.observedPin == null ? 0 : 1) < 2) {
                    continue;
                }
                String taken = location.runWriter == null ? null
                        : selectorOf.get(location.runWriter);
                String observed = null;
                if (location.observedPin != null) {
                    observed = observedArm(location);
                    selectors.add(observed);
                    taken = observed;
                }
                chosen.addAll(location.symbols);
                recordRun(location, selectors, taken, observed, recorded,
                        planted);
                String formula = Arms.exactlyOne(selectors);
                stated.add(formula);
                assertFamily("state_family__" + ordinal + "__"
                                + ArtifactIO.digest(location.key, 12),
                        "(=> " + selector + " " + formula + ")");
            }
            return chosen;
        }

        private String observedArm(StateLocation location) {
            String name = "observed_arm__" + ordinal + "__"
                    + ArtifactIO.digest(location.key + "|" + session, 12);
            lowering.declare(name, VmTermLowering.Sort.BOOL);
            String assertion = "observed_family__" + ordinal + "__"
                    + ArtifactIO.digest(location.key + "|" + session, 12);
            String formula = "(=> " + name + " "
                    + VmTermLowering.and(location.observedPin) + ")";
            stated.add(formula);
            assertFamily(assertion, "(=> " + selector + " " + formula + ")");
            choose(name, ArmChoice.of(assertion, "observed:" + location.key,
                    Collections.<String>emptyList(), session,
                    Collections.<Arms.Arm>emptyList(),
                    Collections.<String, BoundLeaf>emptyMap()));
            return name;
        }

        private void recordRun(StateLocation location, List<String> selectors,
                               String taken, String observed,
                               List<String> recorded,
                               Map<String, String> planted) {
            List<String> plants = new ArrayList<String>();
            if (planted.containsKey(location.key)) {
                String plant = selectorOf.get(planted.get(location.key));
                if (plant != null) plants.add(plant);
                if (observed != null) plants.add(observed);
            }
            String run = plants.isEmpty() ? taken
                    : "(not " + VmTermLowering.or(plants) + ")";
            if (!recorded.contains(run)) recorded.add(run);
            if (!plants.isEmpty()) {
                Map<String, List<String>> world = worldArms.computeIfAbsent(
                        selector, key -> new LinkedHashMap<String,
                                List<String>>());
                List<String> before = world.put(location.key, plants);
                pathUndo.add(() -> restore(world, location.key, before));
            }
            for (String arm : plants.isEmpty()
                    ? Collections.<String>emptyList() : selectors) {
                if (!plants.contains(arm)) own(recordedAtPlants, arm);
            }
        }
    }

    private static List<String> observedPin(List<String> symbols,
                                            Map<String, String> pins) {
        List<String> observedPin = new ArrayList<String>();
        for (String symbol : symbols) {
            String pin = pins.get(symbol);
            if (!observedPin.contains(pin)) observedPin.add(pin);
        }
        return observedPin;
    }

    private boolean seenByAll(List<ReadRow> reads, String session,
                              String location, WriteRow write) {
        if (write == null) return true;
        List<WriteRow> writes = corpus.writesOf(session, location);
        for (ReadRow read : reads) {
            if (!arms.eligible(read.endpoint().occurrence(), session,
                    location, writes, read.observedVersion(), write)) {
                return false;
            }
        }
        return true;
    }

    private static final String INITIAL = "INITIAL|";

    static String writer(WriteRow write) {
        return write.initial()
                ? INITIAL + SmtLowering.locationKey(write.location())
                : write.endpoint().occurrence().id();
    }

    private String received(String symbol, Term delivered, String sent) {
        VmTermLowering.Sort parsed = JavaSmtSorts.sortOfSymbol(symbol);
        String equation = lowering.leafEquals(symbol, parsed, symbol,
                delivered, sent);
        if (equation == null) {
            lowering.leafRefused(symbol, parsed, delivered.sort);
            return null;
        }
        lowering.declareStated(symbol, parsed == null ? delivered.sort
                : parsed);
        return equation;
    }

    private String sentType(String session, String expressionRef) {
        SessionReader reader = corpus.session(session);
        if (reader == null || expressionRef == null) return "";
        return VmTermLowering.expressionJavaType(
                reader.expressions().expression(expressionRef));
    }

    private String initialBody(String session, List<Out> outs) {
        lowering.begin(session, corpus.join(session),
                corpus.expressions(session));
        List<String> conjuncts = new ArrayList<String>();
        boolean stated = true;
        for (Out out : outs) {
            Term value = lower(session, out.arm.expressionRef(),
                    "arm:" + out.arm.slotId(), conjuncts);
            if (value == null) {
                stated = false;
                break;
            }
            String sent = sentType(session, out.arm.expressionRef());
            for (String symbol : out.symbols) {
                if (symbol == null || symbol.isEmpty()) continue;
                String received = received(symbol, value, sent);
                if (received == null) {
                    stated = false;
                    break;
                }
                conjuncts.add(received);
                conjuncts.add(lowering.storeChoice(symbol, out.arm.write()));
            }
        }
        boolean refused = !lowering.openRefusals().isEmpty();
        conjuncts.addAll(lowering.end());
        return stated && !refused ? VmTermLowering.and(conjuncts) : null;
    }

    private static List<Arms.Arm> armsOf(List<Out> outs) {
        List<Arms.Arm> found = new ArrayList<Arms.Arm>();
        for (Out out : outs) found.add(out.arm);
        return found;
    }

    Term lower(String session, String expressionRef, String origin,
               List<String> conditions) {
        SessionReader reader = corpus.session(session);
        if (reader == null || expressionRef == null
                || expressionRef.isEmpty()) {
            return null;
        }
        JsonObject expression = reader.expressions()
                .expression(expressionRef);
        if (expression == null) {
            composer.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    expressionRef, "a row of session " + session + " cites an"
                            + " expression its session's table does not hold:"
                            + " left out");
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
