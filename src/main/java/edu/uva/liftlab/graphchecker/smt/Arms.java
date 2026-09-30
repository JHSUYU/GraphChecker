package edu.uva.liftlab.graphchecker.smt;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * THE family-arm rule, shared by the composer and the flip solver so the two
 * cannot disagree about which deliveries a slot has and what guards them.
 * Nothing here lowers to SMT: arms name expressions by ref and guards by root
 * symbol and value.
 *
 * <ul>
 *   <li><b>Selection (IDENTITY §4)</b> — a WIRE slot's arms are the producer
 *       endpoint's exports from the runs whose OWN pairing named this
 *       consumer, never every export at the endpoint.</li>
 *   <li><b>Guard (CONTRACT-SPEC §4)</b> — the delivering replay's values of
 *       the roots the expression names and of every varied root; never a
 *       clock, never
 *       the prefix's roots (the prefix is already conjoined).</li>
 *   <li><b>Prefix</b> — the producer's decisions with {@code seq} below the
 *       export's.</li>
 *   <li><b>Attestation (IDENTITY §4)</b> — see {@link #attested}; no
 *       witness may move a root inside an unattested arm.</li>
 *   <li><b>Nested handoffs</b> — slots an expression mentions are closed
 *       transitively.</li>
 *   <li><b>STATE eligibility (IDENTITY §4)</b> — see {@link #stateArms}.</li>
 * </ul>
 */
public final class Arms {

    /** What one stage must be able to look up ({@code explore.Corpus}). */
    public interface Rows {
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

        /**
         * What one session RAN one root at, or {@code ""}.  Not the mint's
         * {@code recordedValue}: a planted replay states its value only in
         * its obligation.
         */
        String rootValue(String sessionId, String rootId);

        /**
         * Whether the corpus ran this root at more than one value.  One
         * definition because it decides both what a PATH carries and what an
         * ARM is guarded by, which must agree.
         */
        default boolean varied(String rootId) {
            List<RootMintRow> minted = roots().get(rootId);
            if (minted == null) return false;
            Set<String> values = new LinkedHashSet<String>();
            for (RootMintRow row : minted) {
                String value = rootValue(row.sessionId(), rootId);
                if (value == null || value.isEmpty()) continue;
                values.add(value);
            }
            return values.size() > 1;
        }

        /** The attach that minted this symbol in this session, or null. */
        AttachRow attachOfSymbol(String symbol, String sessionId);

        /** The occurrence this endpoint id belongs to, or null. */
        OccurrenceAddress occurrenceOf(String endpointId);

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
        private final OccurrenceAddress producer;
        private final long deliveredAt;
        private final String producerPathId;
        private final String expressionRef;
        private final List<String> pi;
        private final Map<String, String> guard;
        private final Set<String> guardRoots;
        private final boolean attested;
        private final Set<String> nested;

        Arm(String slotId, String symbol, String sessionId,
            OccurrenceAddress producer, long deliveredAt,
            String producerPathId, String expressionRef, List<String> pi,
            Map<String, String> guard, Set<String> guardRoots,
            boolean attested, Set<String> nested) {
            this.slotId = slotId;
            this.symbol = symbol;
            this.sessionId = sessionId;
            this.producer = producer;
            this.deliveredAt = deliveredAt;
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

        /**
         * The producer occurrence (wire: the interaction's producer; state:
         * the writer).  One selector binds all of one occurrence's outs
         * (PIPELINE §8), so the arm must name it.
         */
        public OccurrenceAddress producer() {
            return producer;
        }

        /**
         * The delivering event's seq: the prefix cutoff.  A selector shared
         * by several outs of one occurrence is taken to the LAST of them.
         */
        public long deliveredAt() {
            return deliveredAt;
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

        /** The root IDS behind that guard, for the manifest and the
         *  attestation rule. */
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
    /** {@code slotId|sessionId|rootId}, in the order the arms were refused. */
    private final Set<String> refusals = new LinkedHashSet<String>();

    public Arms(Rows rows) {
        this.rows = rows;
    }

    /**
     * The arms refused since the last drain, and clears them:
     * those whose expression names a root the delivering session states no
     * mint row for.  Drained, not read, so a caller's gap list never counts
     * one twice.
     */
    public Set<String> drainRefusals() {
        Set<String> drained = new LinkedHashSet<String>(refusals);
        refusals.clear();
        return drained;
    }

    // ------------------------------------------------------------------
    // WIRE slots.
    // ------------------------------------------------------------------

    /**
     * Every arm of ONE wire slot, not closed over {@link Arm#nested}:
     * nested arms belong under the selector of the delivery that names them
     * (PIPELINE §8), which only the caller ({@code ComposedFamilies}) knows.
     *
     * @param symbol the consumer's own variable for this slot
     */
    public List<Arm> armsAt(Interaction slot, String symbol) {
        List<Arm> arms = new ArrayList<Arm>();
        for (AttachRow paired : rows.attachesOf(slot)) {
            // Selection (IDENTITY §4): only a run whose OWN pairing named
            // this consumer; the guard and the attestation are the arm's own.
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

    /**
     * {@link #armsAt} closed transitively over nested slots, as one flat
     * list: the shape a FLIP query wants (no case split).
     */
    public List<Arm> wireArms(Interaction slot, String symbol) {
        List<Arm> arms = new ArrayList<Arm>();
        List<String> queue = new ArrayList<String>();
        Map<String, Interaction> slots =
                new LinkedHashMap<String, Interaction>();
        queue.add(symbol);
        slots.put(symbol, slot);
        Set<String> closed = new LinkedHashSet<String>();
        while (!queue.isEmpty()) {
            String variable = queue.remove(0);
            if (!closed.add(variable)) continue;
            Interaction interaction = slots.get(variable);
            if (interaction == null) continue;
            for (Arm arm : armsAt(interaction, variable)) {
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

    // ------------------------------------------------------------------
    // STATE slots (IDENTITY §4).
    // ------------------------------------------------------------------

    /**
     * Whether a location's owner NAMES one storage cell: a STATIC field, or a
     * heap owner spelled as the VM's symbolic rid
     * ({@code RowPublication.locationKey}).  A rid is per-run, which suffices
     * because alternatives are asked inside one session.  A CLASS owner on a
     * heap location ({@code runtime.SharedStateCapture}) aliases every
     * instance, so such a read is offered no alternative writers.
     */
    public static boolean namedOwner(LocationId location) {
        if (location == null) return false;
        if (location.kind() == LocationKind.STATIC) return true;
        return objectRid(location.owner());
    }

    /** The VM's symbolic rid of one object, as every row spells an owner. */
    private static boolean objectRid(String owner) {
        if (owner == null || owner.isEmpty()) return false;
        for (int index = 0; index < owner.length(); index++) {
            if (!Character.isDigit(owner.charAt(index))) return false;
        }
        return true;
    }

    /**
     * The writer occurrences a read could have seen, as arms (IDENTITY §4): the
     * observed writer plus every ATTESTED writer occurrence HB-concurrent with
     * the reader.  Locks are not constraints.  A writer's writes move as a
     * BLOCK, so there is one arm per writer at its last write of L, and the
     * caller binds every read of L in the reader to it (the arm has no
     * symbol).  The observed writer's arm is the write the read observed:
     * a read that saw STARTING of a writer that then wrote RUNNING never
     * paired with RUNNING, and that arm is the run as it happened.
     *
     * @param readerEndpoint one read of L in the reading occurrence
     * @param session        the reader's own session: eligibility is its
     *                       happens-before and no other run's
     * @param location       the join key of L
     */
    public List<Arm> stateArms(Endpoint readerEndpoint, String session,
                               String location, long observedVersion) {
        OccurrenceAddress reader = readerEndpoint.occurrence();
        // One arm per writer occurrence: the observed write, else the
        // block's last write of L.
        Map<String, WriteRow> armOf = new LinkedHashMap<String, WriteRow>();
        for (WriteRow write : rows.writesOf(session, location)) {
            String key = write.endpoint().occurrence().id();
            WriteRow held = armOf.get(key);
            if (held == null || held.version() != observedVersion
                    && (write.version() == observedVersion
                    || held.seq() < write.seq())) {
                armOf.put(key, write);
            }
        }
        List<Arm> arms = new ArrayList<Arm>();
        for (WriteRow write : armOf.values()) {
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
     * Whether two occurrences of one session are HB-concurrent: neither same
     * thread nor causal-anchor ancestors.  Thread start/join is not in the
     * rows.  Unknown (Lost, unfollowable chain) is NOT concurrent.
     */
    public boolean concurrent(OccurrenceAddress reader,
                              OccurrenceAddress writer, String session) {
        if (reader == null || writer == null) return false;
        if (reader.id().equals(writer.id())) return false;
        if (reader.context().isLost() || writer.context().isLost()) {
            return false;
        }
        if (sameThread(session, reader, writer)) return false;
        if (!chainKnown(session, reader) || !chainKnown(session, writer)) {
            return false;
        }
        return !ancestor(session, writer, reader)
                && !ancestor(session, reader, writer);
    }

    /**
     * Whether this occurrence's anchor chain reaches a Root through
     * endpoints some row places.
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
            // No row states a thread-creation edge (contract.ActivationRow).
            return false;
        }
        return false;
    }

    /**
     * Whether EVENT {@code a} is causally before EVENT {@code b}: same thread
     * by row seq, else along the causal-anchor chain.  Unstated ordering
     * answers {@code false}.
     *
     * <p>The caller passes each row's seq because an endpoint is not an
     * event: a site without a site index shares one endpoint id across all
     * its events in the occurrence, so no single seq per id is right.</p>
     */
    public boolean ancestor(Endpoint a, long aSeq, Endpoint b, long bSeq,
                            String session) {
        if (a == null || b == null) return false;
        OccurrenceAddress left = a.occurrence();
        OccurrenceAddress right = b.occurrence();
        // One thread is one order, whether or not it is one occurrence.
        if (left.id().equals(right.id())
                || sameThread(session, left, right)) {
            // Seq 0 is UNNUMBERED, not "first": both must be numbered.
            return aSeq > 0L && bSeq > 0L && aSeq < bSeq;
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
                // Unplaced: no ordering, so "not before".
                return false;
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
        // The prefix: only decisions taken before the delivery.
        List<String> pi = attested
                ? pathCondition(decisions, deliveredAt)
                : new ArrayList<String>();
        Set<String> symbols = new LinkedHashSet<String>();
        symbolsIn(expression, symbols);
        Map<String, String> guard = new LinkedHashMap<String, String>();
        Set<String> guardRoots = new LinkedHashSet<String>();
        for (Map.Entry<String, List<RootMintRow>> entry
                : rows.roots().entrySet()) {
            RootMintRow row = rows.root(entry.getKey(), session);
            if (row == null) {
                // Refuse, never emit unguarded -- an empty guard would
                // admit the arm under every valuation of this root.
                if (names(symbols, entry.getValue())) {
                    refusals.add(slotId + "|" + session + "|"
                            + entry.getKey());
                    return null;
                }
                continue;
            }
            // Never a clock: its reads are in the prefix already, and pinning
            // it would close every skew witness resting on this arm.
            if (row.kind() == RootKind.CLOCK) continue;
            // Varied roots too, not only the expression's: the arm exists
            // only under the valuation its replay ran.
            if (!rows.varied(entry.getKey())
                    && !symbols.contains(row.symbol())) {
                continue;
            }
            String value = rows.rootValue(session, entry.getKey());
            if (value == null || value.isEmpty()) continue;
            guard.put(row.symbol(), value);
            guardRoots.add(row.rootId());
        }
        Set<String> nested = new LinkedHashSet<String>();
        for (String named : symbols) {
            if (named.equals(symbol)) continue;
            if (rows.attachOfSymbol(named, session) != null) {
                nested.add(named);
            }
        }
        return new Arm(slotId, symbol, session, producer, deliveredAt,
                attested ? rows.pathIdOf(session, producer) : "",
                expressionRef, pi, guard, guardRoots, attested, nested);
    }

    /**
     * Whether an expression's symbols name one root, under any spelling the
     * corpus minted it with.
     */
    private static boolean names(Set<String> symbols,
                                 List<RootMintRow> minted) {
        if (minted == null) return false;
        for (RootMintRow row : minted) {
            if (row.symbol() != null && symbols.contains(row.symbol())) {
                return true;
            }
        }
        return false;
    }

    /**
     * Whether this session STATES the rows of that occurrence: it has an
     * INSTRUMENTED activation row for it.  No decision then means an empty,
     * trivially true prefix, not an absent one.  Trap: whether the occurrence
     * was the replay's FOCUS is irrelevant -- a non-focused instrumented
     * occurrence was still recorded.
     */
    public boolean attested(String session, OccurrenceAddress occurrence) {
        ActivationRow activation = rows.activationOf(session,
                occurrence.id());
        return activation != null && activation.instrumented();
    }

    /**
     * The exports at one producer endpoint made by any session that attests
     * the PRODUCER (not the consumer's session), the seed's first -- the
     * same order as the composer's {@code seedRow}.
     */
    public List<ExportRow> attestedExports(Endpoint producer) {
        List<ExportRow> attested = new ArrayList<ExportRow>();
        if (producer == null) return attested;
        String seed = rows.seedSessionId();
        for (ExportRow export : rows.exportsOf(producer)) {
            if (!attested(export.sessionId(), producer.occurrence())) {
                continue;
            }
            if (seed != null && seed.equals(export.sessionId())) {
                attested.add(0, export);
            } else {
                attested.add(export);
            }
        }
        return attested;
    }

    /**
     * Whether a published term states a predicate.  A CONCRETE branch
     * publishes an empty term, reaching consumers as {@code ""} or
     * {@code "(not )"}; neither is SMT, so both must be omitted.
     */
    public static boolean predicate(String term) {
        String text = term == null ? "" : term.trim();
        return !text.isEmpty() && !"(not )".equals(text);
    }

    /**
     * One path condition, polarity applied: {@code DecisionRow.term} is
     * polarity-free and {@code outcome} says which arm the run took.
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
        return conjunct(decision.term(), decision.outcome());
    }

    /**
     * The polarity rule for an already-rewritten term; the one place it is
     * applied (CONTRACT-SPEC §5).
     */
    public static String conjunct(String term, boolean outcome) {
        return outcome ? term : "(not " + term + ")";
    }

    /**
     * Exactly one of these selectors holds, as a sum of indicators (linear,
     * unlike pairwise exclusion); a single selector is itself.
     */
    public static String exactlyOne(List<String> selectors) {
        if (selectors.size() == 1) return selectors.get(0);
        StringBuilder sum = new StringBuilder("(= (+");
        for (String selector : selectors) {
            sum.append(" (ite ").append(selector).append(" 1 0)");
        }
        return sum.append(") 1)").toString();
    }

    /**
     * Every symbol a recorded expression names, at any depth
     * ({@link ExpressionWalk}; capped at depth 512, it dropped the deeper
     * ones).  Also IMPORT's walk (invariant 11,
     * {@code RowInvariants#attributed}).
     */
    public static void symbolsIn(JsonElement expression, Set<String> into) {
        symbolsIn(expression, into, ExpressionWalk.identitySet());
    }

    /**
     * The same walk over the nodes not in {@code walked} yet: a caller
     * walking many expressions of one table passes one set -- expanded,
     * they share subtrees, and walked as trees one session's table ran
     * IMPORT out of heap (hdfs-11741 v74).
     */
    public static void symbolsIn(JsonElement expression, Set<String> into,
                                 Set<JsonElement> walked) {
        for (ExpressionWalk walk = ExpressionWalk.of(expression, walked);
             walk.hasNext(); ) {
            JsonObject node = walk.next();
            if (VmExpressionIr.SYMBOL_TYPE.equals(
                    VmExpressionIr.typeOf(node))) {
                String raw = JsonFields.optionalString(node, "_exp");
                if (!raw.isEmpty()) into.add(raw);
            }
        }
    }

}
