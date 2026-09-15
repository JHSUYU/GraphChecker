package edu.uva.liftlab.graphchecker.d3.smt;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.d3.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.CausalContext;
import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.Endpoint;
import edu.uva.liftlab.graphchecker.d3.contract.ExportRow;
import edu.uva.liftlab.graphchecker.d3.contract.Interaction;
import edu.uva.liftlab.graphchecker.d3.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.d3.contract.LocationId;
import edu.uva.liftlab.graphchecker.d3.contract.LocationKind;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.d3.contract.WriteRow;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * THE family-arm rule, in one place, for the composer and the flip solver.
 *
 * <p>The rule existed twice -- once here in spirit and once in each stage's
 * own spelling -- and the two disagreed about what guards an arm, which is a
 * way for a flip the explorer proved satisfiable to be refused by the
 * composition that reads the same rows.  So it lives here, and both stages
 * ask.</p>
 *
 * <p>Nothing here lowers anything.  An arm names the expression by its ref,
 * the producer path condition by the terms the runtime published, and the
 * guard by root symbol and value; the stage that wants SMT renders it with
 * the one lowering.  That is deliberate: the rule is about WHICH deliveries
 * a slot has and under what, and none of that is a question about SMT.</p>
 *
 * <p>The settled points, each measured or ruled on:</p>
 * <ul>
 *   <li><b>Selection (R-I2)</b> — the arms of a WIRE slot are the exports at
 *       its producer endpoint from the runs whose OWN pairing named this
 *       consumer endpoint.  Never every export at the endpoint: a producer
 *       replayed many times contributes only where its run paired with this
 *       consumer.</li>
 *   <li><b>Guard (R-GUARD)</b> — exactly the declared roots the delivered
 *       expression mentions, at the delivering replay's values.  Not the
 *       prefix's roots: pi_q is conjoined as the arm's own prefix, so its
 *       root dependence is already inside the arm.  No "varied" filter: an
 *       unvaried root is pinned to its recording everywhere, so guarding on
 *       it is trivially true, and uniformity is worth more than the
 *       conjunct.</li>
 *   <li><b>Prefix</b> — the producer's decisions with {@code seq} below the
 *       export's: what that replay had decided by the time it delivered.</li>
 *   <li><b>Attestation (R-I5)</b> — an arm from a run whose producer
 *       occurrence has no decisions is UNATTESTED: it states what was
 *       delivered, and no witness may move a root inside it.</li>
 *   <li><b>Nested handoffs</b> — a producer forwards what it was handed, so
 *       an expression may mention another slot's variable; those slots are
 *       closed transitively, to a fixed point.</li>
 *   <li><b>STATE eligibility (R-I7.1)</b> — see {@link #stateArms}.</li>
 * </ul>
 */
public final class Arms {

    /** What one stage must be able to look up; both corpora can answer it. */
    public interface Rows {
        /** The sessions of this corpus, in the layout's order. */
        List<String> sessionIds();

        /** The expression this session published under this ref, or null. */
        JsonObject expression(String sessionId, String expressionRef);

        /** The attaches whose own pairing names this interaction. */
        List<AttachRow> attachesOf(Interaction interaction);

        /** The exports at this producer endpoint, any session. */
        List<ExportRow> exportsOf(Endpoint producer);

        /** The writes of this location in this session, any version. */
        List<WriteRow> writesOf(String sessionId, String locationKey);

        /** This session's decisions at this occurrence, in seq order. */
        List<DecisionRow> decisionsOf(String sessionId,
                                      OccurrenceAddress occurrence);

        /** The id this stage gives one session's path at one occurrence. */
        String pathIdOf(String sessionId, OccurrenceAddress occurrence);

        /** This session's mint row for this root, or null. */
        RootMintRow root(String rootId, String sessionId);

        /** Every root the corpus minted, by root id. */
        Map<String, List<RootMintRow>> roots();

        /** The attach that minted this symbol in this session, or null. */
        AttachRow attachOfSymbol(String symbol, String sessionId);

        /** The occurrence this endpoint id belongs to, or null. */
        OccurrenceAddress occurrenceOf(String endpointId);

        /** The session event this endpoint's row was sequenced at, or -1. */
        long seqOf(String sessionId, String endpointId);

        /** This session's activation of that occurrence, or null. */
        ActivationRow activationOf(String sessionId, String occurrenceId);

        /** The session that recorded the run, or null when unanswerable. */
        String seedSessionId();
    }

    /** One delivery a slot records, and what it happened under. */
    public static final class Arm {
        private final String slotId;
        private final String symbol;
        private final String sessionId;
        private final String producerPathId;
        private final String expressionRef;
        private final List<String> pi;
        private final Map<String, String> guard;
        private final Set<String> guardRoots;
        private final boolean attested;
        private final Set<String> nested;

        Arm(String slotId, String symbol, String sessionId,
            String producerPathId, String expressionRef, List<String> pi,
            Map<String, String> guard, Set<String> guardRoots,
            boolean attested, Set<String> nested) {
            this.slotId = slotId;
            this.symbol = symbol;
            this.sessionId = sessionId;
            this.producerPathId = producerPathId;
            this.expressionRef = expressionRef;
            this.pi = Collections.unmodifiableList(pi);
            this.guard = Collections.unmodifiableMap(guard);
            this.guardRoots = Collections.unmodifiableSet(guardRoots);
            this.attested = attested;
            this.nested = Collections.unmodifiableSet(nested);
        }

        /** The slot (interaction id) this arm fills. */
        public String slotId() {
            return slotId;
        }

        /** The variable this arm binds: the consumer's v_H, or the read. */
        public String symbol() {
            return symbol;
        }

        /** The run that delivered it. */
        public String sessionId() {
            return sessionId;
        }

        /** The producer path, or "" when no path condition attests it. */
        public String producerPathId() {
            return producerPathId;
        }

        public String expressionRef() {
            return expressionRef;
        }

        /** The producer's decisions up to the delivery, as published. */
        public List<String> pi() {
            return pi;
        }

        /** Root symbol -> the value the delivering replay ran it at. */
        public Map<String, String> guard() {
            return guard;
        }

        /** The root IDS behind that guard, for the manifest and R-I5. */
        public Set<String> guardRoots() {
            return guardRoots;
        }

        public boolean attested() {
            return attested;
        }

        /** Handoff variables this delivery itself was handed. */
        public Set<String> nested() {
            return nested;
        }

        @Override
        public String toString() {
            return (attested ? "arm " : "unattested arm ") + slotId + " of "
                    + sessionId + " binding " + symbol;
        }
    }

    private final Rows rows;

    public Arms(Rows rows) {
        this.rows = rows;
    }

    // ------------------------------------------------------------------
    // WIRE slots.
    // ------------------------------------------------------------------

    /**
     * Every arm of one WIRE slot, and of every slot reached through it.
     *
     * <p>Closed transitively to a fixed point: a producer forwards what it
     * was itself handed, so an arm's expression may mention another slot's
     * variable, and a variable no family constrains is the one thing a
     * witness must not rest on.</p>
     *
     * @param symbol the consumer's own variable for the first slot
     */
    public List<Arm> wireArms(Interaction slot, String symbol) {
        List<Arm> arms = new ArrayList<Arm>();
        List<String> queue = new ArrayList<String>();
        Map<String, Interaction> slots = new LinkedHashMap<String, Interaction>();
        queue.add(symbol);
        slots.put(symbol, slot);
        Set<String> closed = new LinkedHashSet<String>();
        while (!queue.isEmpty()) {
            String variable = queue.remove(0);
            if (!closed.add(variable)) continue;
            Interaction interaction = slots.get(variable);
            if (interaction == null) continue;
            for (Arm arm : armsOf(interaction, variable)) {
                arms.add(arm);
                for (String nested : arm.nested()) {
                    if (nested.equals(variable)) continue;
                    AttachRow source = rows.attachOfSymbol(nested,
                            arm.sessionId());
                    if (source == null || source.interaction() == null) {
                        continue;
                    }
                    slots.put(nested, source.interaction());
                    queue.add(nested);
                }
            }
        }
        return arms;
    }

    /** The arms of one slot: R-I2 selection, R-GUARD guard, R-I5 flag. */
    private List<Arm> armsOf(Interaction slot, String symbol) {
        List<Arm> arms = new ArrayList<Arm>();
        for (AttachRow paired : rows.attachesOf(slot)) {
            // R-I2: only a run whose OWN pairing named this consumer.
            String session = paired.sessionId();
            for (ExportRow export : rows.exportsOf(slot.producer())) {
                if (!export.sessionId().equals(session)) continue;
                Arm arm = arm(slot.id(), symbol, session,
                        slot.producer().occurrence(), export.expressionRef(),
                        export.seq());
                if (arm != null) arms.add(arm);
            }
        }
        return arms;
    }

    // ------------------------------------------------------------------
    // STATE slots (R-I7.1).
    // ------------------------------------------------------------------

    /**
     * The writer occurrences a read could have seen, as arms.
     *
     * <p>Not "versions earlier by seq": the alternatives for a reader
     * occurrence R on location L are the writer OCCURRENCES that are
     * HB-CONCURRENT with R -- not ordered against it by program order, by
     * message causality along the causal-anchor chain, or by thread
     * start/join.  Locks are not constraints: a lock orders the two
     * executions that took it, not the two the checker is asking about.</p>
     *
     * <p>A writer's writes to L move as a BLOCK -- wholly before or wholly
     * after R -- so there is one arm per writer occurrence, binding to that
     * occurrence's last write of L, and every read of L inside R takes the
     * same arm.  A writer interposed between two reads of one occurrence is
     * not an interleaving this rule admits.</p>
     *
     * <p>Only ATTESTED writer occurrences are alternatives.  An unattested
     * writer, or one whose causal context is Lost, states its delivery and
     * no more: with no path condition behind it nothing says the delivery
     * would survive a move, and with no context HB is unknown, which is not
     * the same as concurrent.</p>
     *
     * <p>An arm carries no symbol: the caller binds every read of L in the
     * reader occurrence to the arm's expression, which is what "the block"
     * means in the formula.</p>
     *
     * @param readerEndpoint one read of L in the reading occurrence
     * @param session        the reader's own session: eligibility is its
     *                       happens-before and no other run's
     * @param location       the join key of L
     */
    /**
     * Whether a location's owner NAMES its storage across replays.
     *
     * <p>IDENTITY-V3 sec 5 (Memory Indexing): the three owner forms that
     * name one storage are the allocating {@link Endpoint}'s id, the
     * {@code preWindow:} form for an object older than the window, and --
     * for a STATIC field only -- the class, which owns exactly one cell.
     * Anything else is a name that is not an identity: a session rid is
     * that run's counter and means nothing in another run, and a CLASS on
     * a heap location aliases every instance of it at once.</p>
     *
     * <p>What follows is the whole use of it: alternatives (R-I7.1) are
     * computed only where the owner names the storage.  A read on an
     * aliasing owner gets its delivery and nothing else -- choosing among
     * "writers" that may be writes to a different object is how a witness
     * is invented rather than found.</p>
     */
    public static boolean namedOwner(LocationId location) {
        if (location == null) return false;
        if (location.preWindow()) return true;
        if (location.kind() == LocationKind.STATIC) return true;
        return allocationId(location.owner());
    }

    /** An allocation Endpoint id: sha16, optionally with its m-th object. */
    private static boolean allocationId(String owner) {
        if (owner == null) return false;
        String digest = owner;
        int at = owner.indexOf('#');
        if (at >= 0) {
            digest = owner.substring(0, at);
            String ordinal = owner.substring(at + 1);
            if (ordinal.isEmpty()) return false;
            for (int index = 0; index < ordinal.length(); index++) {
                if (!Character.isDigit(ordinal.charAt(index))) return false;
            }
        }
        if (digest.length() != 16) return false;
        for (int index = 0; index < digest.length(); index++) {
            char value = digest.charAt(index);
            boolean hex = value >= '0' && value <= '9'
                    || value >= 'a' && value <= 'f';
            if (!hex) return false;
        }
        return true;
    }

    public List<Arm> stateArms(Endpoint readerEndpoint, String session,
                               String location, long observedVersion) {
        OccurrenceAddress reader = readerEndpoint.occurrence();
        // One arm per writer occurrence: the block, at its last write of L.
        Map<String, WriteRow> lastByOccurrence =
                new LinkedHashMap<String, WriteRow>();
        for (WriteRow write : rows.writesOf(session, location)) {
            String key = write.endpoint().occurrence().id();
            WriteRow held = lastByOccurrence.get(key);
            if (held == null || held.seq() < write.seq()) {
                lastByOccurrence.put(key, write);
            }
        }
        List<Arm> arms = new ArrayList<Arm>();
        for (WriteRow write : lastByOccurrence.values()) {
            OccurrenceAddress writer = write.endpoint().occurrence();
            boolean observed = write.version() == observedVersion;
            if (!observed && !concurrent(reader, writer, session)) continue;
            Arm arm = arm(Interaction.of(InteractionKind.STATE,
                            write.endpoint(), readerEndpoint).id(),
                    "", session, writer, write.expressionRef(),
                    write.seq());
            if (arm == null) continue;
            // An alternative must be attested; the observed writer is stated
            // whatever it is, because it is what the run did.
            if (!observed && !arm.attested()) continue;
            arms.add(arm);
        }
        return arms;
    }

    /**
     * Whether two occurrences of one session are HB-concurrent.
     *
     * <p>The three orderings the rows can state: program order (one
     * occurrence is the other), message causality (one is an ancestor of the
     * other along the causal-anchor chain), and thread start/join -- which
     * the rows do not carry today, and its absence is stated here rather
     * than assumed away.  A Lost context answers "unknown", and unknown is
     * not concurrent.</p>
     */
    public boolean concurrent(OccurrenceAddress reader,
                              OccurrenceAddress writer, String session) {
        if (reader == null || writer == null) return false;
        if (reader.id().equals(writer.id())) return false;
        if (reader.context().isLost() || writer.context().isLost()) {
            return false;
        }
        // Unknown is not concurrent.  A causal chain this corpus cannot
        // follow to its root -- an anchor naming a producer endpoint no row
        // places -- leaves the ordering unstated, and an unstated ordering
        // is not permission to reorder.
        if (sameThread(session, reader, writer)) return false;
        if (!chainKnown(session, reader) || !chainKnown(session, writer)) {
            return false;
        }
        return !ancestor(session, writer, reader)
                && !ancestor(session, reader, writer);
    }

    /**
     * Whether this occurrence's causal chain is followable to its root.
     *
     * <p>Every anchor on the way must name a producer endpoint some row of
     * this corpus places, and the chain must end at a Root -- a workload
     * action or a daemon tick.  A chain that ends at a Lost context, or at
     * an endpoint nothing places, states no ordering.</p>
     */
    private boolean chainKnown(String session,
                               OccurrenceAddress occurrence) {
        Set<String> seen = new LinkedHashSet<String>();
        OccurrenceAddress at = occurrence;
        while (at != null && seen.add(at.id())) {
            if (at.context().form() == CausalContext.Form.ROOT) return true;
            if (at.context().form() == CausalContext.Form.ANCHOR) {
                at = rows.occurrenceOf(((CausalContext.Anchor) at.context())
                        .producerEndpointId());
                continue;
            }
            // A context the chain cannot name may still be placed by the
            // thread that started it.
            Endpoint starter = startedBy(session, at);
            if (starter == null) return false;
            at = starter.occurrence();
        }
        return false;
    }

    /**
     * Whether {@code a} is causally before {@code b} in this session.
     *
     * <p>Three orderings, in the order they can be asked of the rows: inside
     * one occurrence, the session's own event order (same-thread program
     * order); across occurrences, the causal-anchor chain -- the occurrence
     * that started the other's request is before it; and thread start/join,
     * which the rows carry only as that chain today.  An ordering the rows
     * do not state is UNKNOWN, and unknown is answered {@code false} here,
     * so a caller asking "is a before b" never reads absence as order.</p>
     */
    public boolean ancestor(Endpoint a, Endpoint b, String session) {
        if (a == null || b == null) return false;
        OccurrenceAddress left = a.occurrence();
        OccurrenceAddress right = b.occurrence();
        // One thread is one order, whether or not it is one occurrence: two
        // activations the runtime ran on the same thread cannot interleave
        // with each other, and the session's event order says which came
        // first.
        if (left.id().equals(right.id())
                || sameThread(session, left, right)) {
            long first = rows.seqOf(session, a.id());
            long second = rows.seqOf(session, b.id());
            return first >= 0L && second >= 0L && first < second;
        }
        if (!chainKnown(session, left) || !chainKnown(session, right)) {
            return false;
        }
        return ancestor(session, left, right);
    }

    /** Whether one session ran these two occurrences on one thread. */
    private boolean sameThread(String session, OccurrenceAddress left,
                               OccurrenceAddress right) {
        String one = threadKey(session, left);
        String other = threadKey(session, right);
        return !one.isEmpty() && one.equals(other);
    }

    private String threadKey(String session, OccurrenceAddress occurrence) {
        ActivationRow activation = rows.activationOf(session,
                occurrence.id());
        return activation == null || activation.threadKey() == null
                ? "" : activation.threadKey();
    }

    /** The endpoint that started the thread this occurrence ran on. */
    private Endpoint startedBy(String session,
                               OccurrenceAddress occurrence) {
        ActivationRow activation = rows.activationOf(session,
                occurrence.id());
        return activation == null ? null : activation.startedBy();
    }

    /** Whether {@code older} starts the request {@code younger} runs in. */
    private boolean ancestor(String session, OccurrenceAddress older,
                             OccurrenceAddress younger) {
        Set<String> seen = new LinkedHashSet<String>();
        OccurrenceAddress at = younger;
        while (at != null && seen.add(at.id())) {
            OccurrenceAddress parent = null;
            if (at.context().form() == CausalContext.Form.ANCHOR) {
                parent = rows.occurrenceOf(((CausalContext.Anchor)
                        at.context()).producerEndpointId());
            }
            if (parent == null) {
                // The thread this one runs on was started by somebody, and
                // everything that somebody had already done is before it.
                Endpoint starter = startedBy(session, at);
                if (starter == null) return false;
                if (starter.occurrence().id().equals(older.id())) return true;
                parent = starter.occurrence();
            } else if (parent.id().equals(older.id())) {
                return true;
            }
            at = parent;
        }
        return false;
    }

    // ------------------------------------------------------------------
    // One arm.
    // ------------------------------------------------------------------

    private Arm arm(String slotId, String symbol, String session,
                    OccurrenceAddress producer, String expressionRef,
                    long deliveredAt) {
        JsonObject expression = rows.expression(session, expressionRef);
        if (expression == null) return null;
        List<DecisionRow> decisions = rows.decisionsOf(session, producer);
        boolean attested = attested(session, producer);
        // The prefix: what the replay had decided BY THE TIME it delivered.
        // A decision it took afterwards is not a reason the delivery
        // happened.
        List<String> pi = attested
                ? pathCondition(decisions, deliveredAt)
                : new ArrayList<String>();
        Set<String> symbols = new LinkedHashSet<String>();
        symbolsIn(expression, symbols, 0);
        Map<String, String> guard = new LinkedHashMap<String, String>();
        Set<String> guardRoots = new LinkedHashSet<String>();
        for (Map.Entry<String, List<RootMintRow>> entry
                : rows.roots().entrySet()) {
            RootMintRow row = rows.root(entry.getKey(), session);
            if (row == null) continue;
            if (!symbols.contains(row.symbol())) continue;
            if (row.recordedValue() == null
                    || row.recordedValue().isEmpty()) {
                continue;
            }
            guard.put(row.symbol(), row.recordedValue());
            guardRoots.add(row.rootId());
        }
        Set<String> nested = new LinkedHashSet<String>();
        for (String named : symbols) {
            if (named.equals(symbol)) continue;
            if (rows.attachOfSymbol(named, session) != null) {
                nested.add(named);
            }
        }
        return new Arm(slotId, symbol, session,
                attested ? rows.pathIdOf(session, producer) : "",
                expressionRef, pi, guard, guardRoots, attested, nested);
    }

    /**
     * Whether this session explored that occurrence symbolically.
     *
     * <p>An arm is ATTESTED when the recording can say what the producer
     * would have done, not merely what it did -- and that is a property of
     * how the replay ran it, not of how many branches it happened to meet.
     * The activation must be INSTRUMENTED, and the occurrence must have run
     * symbolically in this session: in the seed, where every instrumented
     * region is symbolic, or as the focus of the task that drove an
     * exploration replay.  A symbolic straight-line region with no decision
     * at all is attested, which "has decisions" got wrong; decisions
     * present remain a corroboration and never the criterion.</p>
     */
    public boolean attested(String session, OccurrenceAddress occurrence) {
        ActivationRow activation = rows.activationOf(session,
                occurrence.id());
        if (activation == null || !activation.instrumented()) return false;
        if (activation.focused()) return true;
        String seed = rows.seedSessionId();
        return seed != null && seed.equals(session);
    }

    /**
     * One path condition, with each decision's polarity applied.
     *
     * <p>{@code DecisionRow.term} is the branch PREDICATE as written at the
     * site, polarity-free: the same site in two replays publishes the same
     * term and the two runs differ in {@code outcome}.  So the conjunct is
     * the term when the run took it and its negation when it did not, and
     * every consumer applies that -- here, once, because a consumer that
     * forgot it would state a path that took the arm its run did not.</p>
     *
     * @param before only decisions the session sequenced before this, or
     *               {@link Long#MAX_VALUE} for the whole path
     */
    public static List<String> pathCondition(List<DecisionRow> decisions,
                                             long before) {
        List<String> pi = new ArrayList<String>();
        if (decisions == null) return pi;
        for (DecisionRow decision : decisions) {
            if (decision.seq() >= before) continue;
            pi.add(conjunct(decision));
        }
        return pi;
    }

    /** One decision, as the arm of it that its run took. */
    public static String conjunct(DecisionRow decision) {
        String term = decision.term();
        return decision.outcome() ? term : "(not " + term + ")";
    }

    /** Every symbol a recorded expression names, whatever its depth. */
    static void symbolsIn(JsonElement expression, Set<String> into,
                          int depth) {
        if (expression == null || expression.isJsonNull() || depth > 512) {
            return;
        }
        if (expression.isJsonArray()) {
            for (JsonElement child : expression.getAsJsonArray()) {
                symbolsIn(child, into, depth + 1);
            }
            return;
        }
        if (!expression.isJsonObject()) return;
        JsonObject node = expression.getAsJsonObject();
        if ("SymbolExpression".equals(JsonFields.optionalString(node,
                "_type"))) {
            String raw = JsonFields.optionalString(node, "_exp");
            if (!raw.isEmpty()) into.add(raw);
        }
        for (String member : node.keySet()) {
            JsonElement child = node.get(member);
            if (child == null || child.isJsonPrimitive()) continue;
            if (child.isJsonArray()) {
                JsonArray array = child.getAsJsonArray();
                for (JsonElement item : array) {
                    symbolsIn(item, into, depth + 1);
                }
                continue;
            }
            symbolsIn(child, into, depth + 1);
        }
    }

}
