package edu.uva.liftlab.graphchecker.smt;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RowOrder;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Pattern;

public final class Arms {

    public interface Rows {
        JsonObject expression(String sessionId, String expressionRef);

        List<AttachRow> attachesOf(Interaction interaction);

        List<ExportRow> exportsOf(Endpoint producer);

        default List<AttachRow> ownAttachesOf(String sessionId,
                                              Interaction interaction) {
            return Collections.emptyList();
        }

        default List<ExportRow> ownExportsOf(String sessionId,
                                             Endpoint producer) {
            return Collections.emptyList();
        }

        List<WriteRow> writesOf(String sessionId, String locationKey);

        List<ReadRow> readsOf(String sessionId, String locationKey);

        List<DecisionRow> decisionsOf(String sessionId,
                                      OccurrenceAddress occurrence);

        String pathIdOf(String sessionId, OccurrenceAddress occurrence);

        RootMintRow root(String rootId, String sessionId);

        RootMintRow ranRoot(String rootId, String sessionId);

        Map<String, List<RootMintRow>> roots();

        default long forcedFrom(String sessionId) {
            return Long.MAX_VALUE;
        }

        String rootValue(String sessionId, String rootId);

        boolean varied(String rootId);

        AttachRow attachOfSymbol(String symbol, String sessionId);

        OccurrenceAddress occurrenceOf(String endpointId);

        ActivationRow activationOf(String sessionId, String occurrenceId);

        String seedSessionId();
    }

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
        private final Map<String, RootMintRow> guardMints;
        private final boolean attested;
        private final Set<String> nested;
        private final WriteRow write;
        private final AttachRow attach;

        Arm(String slotId, String symbol, String sessionId,
            OccurrenceAddress producer, long deliveredAt,
            String producerPathId, String expressionRef, List<String> pi,
            Map<String, String> guard, Map<String, RootMintRow> guardMints,
            boolean attested, Set<String> nested, WriteRow write,
            AttachRow attach) {
            this.slotId = slotId;
            this.symbol = symbol;
            this.sessionId = sessionId;
            this.producer = producer;
            this.deliveredAt = deliveredAt;
            this.producerPathId = producerPathId;
            this.expressionRef = expressionRef;
            this.pi = Collections.unmodifiableList(pi);
            this.guard = Collections.unmodifiableMap(guard);
            this.guardMints = Collections.unmodifiableMap(guardMints);
            this.attested = attested;
            this.nested = Collections.unmodifiableSet(nested);
            this.write = write;
            this.attach = attach;
        }

        public String slotId() {
            return slotId;
        }

        public String symbol() {
            return symbol;
        }

        public String sessionId() {
            return sessionId;
        }

        public OccurrenceAddress producer() {
            return producer;
        }

        public long deliveredAt() {
            return deliveredAt;
        }

        public String producerPathId() {
            return producerPathId;
        }

        public String expressionRef() {
            return expressionRef;
        }

        public List<String> pi() {
            return pi;
        }

        public Map<String, String> guard() {
            return guard;
        }

        public Map<String, RootMintRow> guardMints() {
            return guardMints;
        }

        public Set<String> guardRoots() {
            Set<String> ids = new LinkedHashSet<String>();
            for (RootMintRow mint : guardMints.values()) ids.add(mint.rootId());
            return ids;
        }

        public boolean attested() {
            return attested;
        }

        public Set<String> nested() {
            return nested;
        }

        public WriteRow write() {
            return write;
        }

        public AttachRow attach() {
            return attach;
        }

        @Override
        public String toString() {
            return (attested ? "arm " : "unattested arm ") + slotId + " of "
                    + sessionId + " binding " + symbol;
        }
    }

    private static final Pattern THREAD_ENTRY =
            Pattern.compile("#u\\d+$|: void run\\(\\)>$");

    private final Rows rows;
    private final Map<String, NavigableSet<Long>> unrowed =
            new ConcurrentHashMap<String, NavigableSet<Long>>();
    private final ThreadLocal<Set<String>> refusals =
            ThreadLocal.withInitial(LinkedHashSet::new);
    private final Map<String, Set<String>> symbolsByExpression =
            new ConcurrentHashMap<String, Set<String>>();
    private final Map<String, List<RootGuard>> rootGuards =
            new ConcurrentHashMap<String, List<RootGuard>>();
    private final Map<String, Boolean> constructed =
            new ConcurrentHashMap<String, Boolean>();

    public Arms(Rows rows) {
        this.rows = rows;
    }

    public Set<String> drainRefusals() {
        Set<String> held = refusals.get();
        Set<String> drained = new LinkedHashSet<String>(held);
        held.clear();
        return drained;
    }


    public List<Arm> armsAt(Interaction slot, String symbol, String scope) {
        return armsAt(slot, symbol, scope, null);
    }

    public List<Arm> ownArmsAt(Interaction slot, String symbol,
                               String session) {
        return armsAt(slot, symbol, session, session);
    }

    private List<Arm> armsAt(Interaction slot, String symbol, String scope,
                             String only) {
        List<Arm> arms = new ArrayList<Arm>();
        for (Pairing pairing : pairings(slot, scope, only)) {
            Arm arm = arm(slot.id(), symbol, pairing.attach.sessionId(),
                    slot.producer().occurrence(),
                    pairing.export.expressionRef(), pairing.export.seq(),
                    null, pairing.attach);
            if (arm != null) arms.add(arm);
        }
        return arms;
    }

    private static final class Pairing {
        final AttachRow attach;
        final ExportRow export;

        Pairing(AttachRow attach, ExportRow export) {
            this.attach = attach;
            this.export = export;
        }
    }

    private List<Pairing> pairings(Interaction slot, String scope,
                                   String only) {
        List<Pairing> pairings = new ArrayList<Pairing>();
        List<AttachRow> attaches = new ArrayList<AttachRow>(
                rows.attachesOf(slot));
        attaches.addAll(rows.ownAttachesOf(scope, slot));
        for (AttachRow paired : attaches) {
            String session = paired.sessionId();
            if (only != null && !only.equals(session)) continue;
            List<ExportRow> own = rows.ownExportsOf(session, slot.producer());
            for (List<ExportRow> exports : Arrays.asList(
                    rows.exportsOf(slot.producer()), own)) {
                for (ExportRow export : exports) {
                    if (!export.sessionId().equals(session)) continue;
                    pairings.add(new Pairing(paired, export));
                }
            }
        }
        return pairings;
    }

    public List<ExportRow> attestedDeliveries(Interaction slot,
                                              String scope) {
        List<ExportRow> attested = new ArrayList<ExportRow>();
        if (slot == null || slot.producer() == null) return attested;
        String seed = rows.seedSessionId();
        Set<String> seen = new HashSet<String>();
        for (Pairing pairing : pairings(slot, scope, null)) {
            ExportRow export = pairing.export;
            if (!attested(export.sessionId(), slot.producer().occurrence())
                    || !seen.add(export.sessionId() + "#" + export.seq())) {
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

    public List<Arm> wireArms(Interaction slot, String symbol, String scope) {
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
            for (Arm arm : armsAt(interaction, variable, scope)) {
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


    public static boolean namedOwner(LocationId location) {
        if (location == null) return false;
        if (location.kind() == LocationKind.STATIC
                || location.kind() == LocationKind.VIEW) {
            return true;
        }
        return objectRid(location.owner());
    }

    private static boolean objectRid(String owner) {
        if (owner == null || owner.isEmpty()) return false;
        for (int index = 0; index < owner.length(); index++) {
            if (!Character.isDigit(owner.charAt(index))) return false;
        }
        return true;
    }

    public List<Arm> stateArms(Endpoint readerEndpoint, String session,
                               String location, long observedVersion,
                               boolean alternatives) {
        OccurrenceAddress reader = readerEndpoint.occurrence();
        List<WriteRow> writes = rows.writesOf(session, location);
        List<Arm> arms = new ArrayList<Arm>();
        Map<String, WriteRow> armOf = new LinkedHashMap<String, WriteRow>();
        for (WriteRow write : writes) {
            if (write.initial()) {
                if (write.version() == observedVersion || alternatives
                                && eligible(reader, session, location, writes,
                        observedVersion, write)) {
                    Arm arm = arm(slot(write, readerEndpoint), "", session,
                            write.endpoint().occurrence(),
                            write.expressionRef(), write.seq(), write, null);
                    if (arm != null) arms.add(arm);
                }
                continue;
            }
            String key = write.endpoint().occurrence().id();
            WriteRow held = armOf.get(key);
            if (held == null || held.version() != observedVersion
                    && (write.version() == observedVersion
                    || RowOrder.compare(held, write) < 0)) {
                armOf.put(key, write);
            }
        }
        for (WriteRow write : armOf.values()) {
            OccurrenceAddress writer = write.endpoint().occurrence();
            boolean observed = write.version() == observedVersion;
            if (!observed && (!alternatives || !eligible(reader, session,
                    location, writes, observedVersion, write))) {
                continue;
            }
            Arm arm = arm(slot(write, readerEndpoint), "", session, writer,
                    write.expressionRef(), write.seq(), write, null);
            if (arm == null) continue;
            if (!observed && !arm.attested()) continue;
            arms.add(arm);
        }
        return arms;
    }

    private static String slot(WriteRow write, Endpoint reader) {
        return Interaction.of(InteractionKind.STATE, write.endpoint(), reader)
                .id();
    }

    public boolean eligible(OccurrenceAddress reader, String session,
                            String location, List<WriteRow> writes,
                            long observedVersion, WriteRow state) {
        if (state.version() == observedVersion) return true;
        if (!RowOrder.beforeEvent(state.seq(), state.tie(),
                rows.forcedFrom(session))) {
            return false;
        }
        if (!state.initial() && (constructs(state) || !concurrent(reader,
                state.endpoint().occurrence(), session))) {
            return false;
        }
        long low = Math.min(state.version(), observedVersion);
        long high = Math.max(state.version(), observedVersion);
        Long between = unrowed(session, location, writes).higher(low);
        if (between != null && between < high) return false;
        boolean overtaking = !state.initial()
                && state.version() < observedVersion;
        for (WriteRow write : writes) {
            if (write.initial() || write.version() <= low
                    || write.version() > high) {
                continue;
            }
            if (constructs(write)) return false;
            OccurrenceAddress occurrence = write.endpoint().occurrence();
            if (concurrent(reader, occurrence, session)) continue;
            if (overtaking && concurrent(state.endpoint().occurrence(),
                    occurrence, session)) {
                continue;
            }
            return false;
        }
        return true;
    }

    private NavigableSet<Long> unrowed(String session, String location,
                                       List<WriteRow> writes) {
        return unrowed.computeIfAbsent(session + "|" + location, key -> {
            Set<Long> rowed = new HashSet<Long>();
            for (WriteRow write : writes) rowed.add(write.version());
            NavigableSet<Long> seen = new TreeSet<Long>();
            for (ReadRow read : rows.readsOf(session, location)) {
                if (read.observedVersion() >= 0L
                        && !rowed.contains(read.observedVersion())) {
                    seen.add(read.observedVersion());
                }
            }
            return seen;
        });
    }

    private boolean constructs(WriteRow write) {
        return constructed.computeIfAbsent(write.endpoint().id(),
                key -> constructedAt(write));
    }

    private static boolean constructedAt(WriteRow write) {
        if (constructing(write.endpoint().site())) return true;
        List<Frame> frames = write.endpoint().siteIndex().frames();
        for (int at = frames.size() - 1; at >= 0; at--) {
            String site = frames.get(at).callSite();
            if (constructing(site)) return true;
            if (THREAD_ENTRY.matcher(site).find()) return false;
        }
        return false;
    }

    private static boolean constructing(String site) {
        return site.contains("<init>(") || site.contains("<clinit>(");
    }

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
            return false;
        }
        return false;
    }

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
                return false;
            } else if (parent.id().equals(older.id())) {
                return true;
            }
            at = parent;
        }
        return false;
    }


    private Arm arm(String slotId, String symbol, String session,
                    OccurrenceAddress producer, String expressionRef,
                    long deliveredAt, WriteRow write, AttachRow attach) {
        JsonObject expression = rows.expression(session, expressionRef);
        if (expression == null) return null;
        boolean initial = write != null && write.initial();
        boolean attested = initial || attested(session, producer);
        List<String> pi = attested && !initial
                ? pathCondition(rows.decisionsOf(session, producer),
                deliveredAt)
                : new ArrayList<String>();
        Set<String> symbols = symbolsByExpression.computeIfAbsent(
                session + " " + expressionRef, key -> {
                    Set<String> named = new LinkedHashSet<String>();
                    symbolsIn(expression, named);
                    return Collections.unmodifiableSet(named);
                });
        Map<String, String> guard = new LinkedHashMap<String, String>();
        Map<String, RootMintRow> guardMints =
                new LinkedHashMap<String, RootMintRow>();
        for (RootGuard root : rootGuards(session)) {
            if (root.ran == null) {
                if (!Collections.disjoint(symbols, root.minted)) {
                    refusals.get().add(slotId + "|" + session + "|"
                            + root.rootId);
                    return null;
                }
                continue;
            }
            if (root.ifNamed && !symbols.contains(root.ran.symbol())) {
                continue;
            }
            guard.put(root.ran.symbol(), root.value);
            guardMints.put(root.ran.symbol(), root.ran);
        }
        Set<String> nested = new LinkedHashSet<String>();
        for (String named : symbols) {
            if (named.equals(symbol)) continue;
            if (rows.attachOfSymbol(named, session) != null) {
                nested.add(named);
            }
        }
        return new Arm(slotId, symbol, session, producer, deliveredAt,
                attested && !initial ? rows.pathIdOf(session, producer) : "",
                expressionRef, pi, guard, guardMints, attested, nested,
                write, attach);
    }

    private static final class RootGuard {
        final String rootId;
        final RootMintRow ran;
        final Set<String> minted;
        final boolean ifNamed;
        final String value;

        RootGuard(String rootId, RootMintRow ran, Set<String> minted,
                  boolean ifNamed, String value) {
            this.rootId = rootId;
            this.ran = ran;
            this.minted = minted;
            this.ifNamed = ifNamed;
            this.value = value;
        }
    }

    private List<RootGuard> rootGuards(String session) {
        List<RootGuard> held = rootGuards.get(session);
        if (held != null) return held;
        List<RootGuard> guards = new ArrayList<RootGuard>();
        for (Map.Entry<String, List<RootMintRow>> entry
                : rows.roots().entrySet()) {
            String rootId = entry.getKey();
            RootMintRow row = rows.ranRoot(rootId, session);
            if (row == null) {
                Set<String> minted = new HashSet<String>();
                for (RootMintRow mint : entry.getValue()) {
                    if (mint.symbol() != null) minted.add(mint.symbol());
                }
                if (!minted.isEmpty()) {
                    guards.add(new RootGuard(rootId, null, minted, false,
                            null));
                }
                continue;
            }
            if (row.kind() == RootKind.CLOCK) continue;
            String value = rows.rootValue(session, rootId);
            if (value == null || value.isEmpty()) continue;
            guards.add(new RootGuard(rootId, row, null,
                    rows.root(rootId, session) != null
                            && !rows.varied(rootId), value));
        }
        guards = Collections.unmodifiableList(guards);
        rootGuards.put(session, guards);
        return guards;
    }

    public boolean attested(String session, OccurrenceAddress occurrence) {
        ActivationRow activation = rows.activationOf(session,
                occurrence.id());
        return activation != null && activation.instrumented();
    }

    public static boolean predicate(String term) {
        String text = term == null ? "" : term.trim();
        return !text.isEmpty() && !"(not )".equals(text);
    }

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

    public static String conjunct(DecisionRow decision) {
        return conjunct(decision.term(), decision.outcome());
    }

    public static String conjunct(String term, boolean outcome) {
        return outcome ? term : "(not " + term + ")";
    }

    public static String exactlyOne(List<String> selectors) {
        if (selectors.size() == 1) return selectors.get(0);
        StringBuilder sum = new StringBuilder("(= (+");
        for (String selector : selectors) {
            sum.append(" (ite ").append(selector).append(" 1 0)");
        }
        return sum.append(") 1)").toString();
    }

    public static void symbolsIn(JsonElement expression, Set<String> into) {
        symbolsIn(expression, into, ExpressionWalk.identitySet());
    }

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
