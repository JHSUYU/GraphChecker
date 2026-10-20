package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;

import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Reason;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Term;
import edu.uva.liftlab.graphchecker.contract.ContentPort;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.contract.FrozenSet;
import edu.uva.liftlab.graphchecker.contract.Held;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.OpenSet;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowOrder;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.VersionMap;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.ExpressionWalk;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.FloatingKind;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.IntegralWidth;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.SExpression;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.smt.VmRows;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.BiPredicate;
import java.util.function.Supplier;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.and;
import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.expressionJavaType;
import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.floatingKind;
import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.numeric;
import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.or;
import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.smtLiteral;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.primitiveString;
import static edu.uva.liftlab.graphchecker.smt.VmExpressionIr.arithmetic;
import static edu.uva.liftlab.graphchecker.smt.VmExpressionIr.arithmeticOperator;
import static edu.uva.liftlab.graphchecker.smt.VmExpressionIr.bitwiseOperator;
import static edu.uva.liftlab.graphchecker.smt.VmExpressionIr.comparison;
import static edu.uva.liftlab.graphchecker.smt.VmExpressionIr.constantPayload;
import static edu.uva.liftlab.graphchecker.smt.VmExpressionIr.quote;
import static edu.uva.liftlab.graphchecker.smt.VmExpressionIr.shiftOperator;

public final class SmtLowering {

    public static final String CUT = "PROPAGATION_CUT";
    public static final String UNSTATED = "UNSTATED_VALUE";
    public static final String SORT_CONFLICT = "SORT_CONFLICT";
    static final String REFERENCE = "EXPR.";
    private static final int REFERENCE_ROUNDS = 4;

    public interface SessionJoin {
        JsonElement writeExpression(String locationKey, long version);

        default WriteRow write(String locationKey, long version) {
            return null;
        }

        List<WriteRow> writes(String locationKey);

        List<ReadRow> reads(String locationKey);

        Set<String> mintedReadSymbols(long version);

        Set<String> readSymbols(String locationKey, long version);

        boolean moves(String symbol);

        boolean repaired(String locationKey, long readEvent);

        boolean concurrent(OccurrenceAddress reader,
                           OccurrenceAddress writer);

        default RefusalFrame frame(String occurrenceId) {
            return null;
        }

        default ViewLeaf viewLeaf(String symbol) {
            return null;
        }

        default String viewLeafAt(String viewKey, long version,
                                  String port) {
            return null;
        }

        default RefusalFrame frameOfWrite(String locationKey, long version) {
            return null;
        }
    }

    public static final class RefusalFrame {
        public final String producer;
        final List<JsonElement> exports;
        public final String refusal;

        RefusalFrame(String producer, List<JsonElement> exports,
                     String refusal) {
            this.producer = producer;
            this.exports = Collections.unmodifiableList(exports);
            this.refusal = refusal;
        }
    }

    public Set<String> frameMovers(RefusalFrame frame) {
        Set<String> moving = new LinkedHashSet<String>();
        for (JsonElement export : frame.exports) {
            moving.addAll(movers(export, true));
        }
        return moving;
    }

    public Set<String> framedLeaves() {
        return Collections.unmodifiableSet(framedLeaves);
    }

    private static final Pattern REFUSED_HANDLE =
            Pattern.compile("refused the attach of handle ([0-9]+)");

    public static final class ViewLeaf {
        public final String viewKey;
        public final long version;
        public final String port;

        public ViewLeaf(String viewKey, long version, String port) {
            this.viewKey = viewKey;
            this.version = version;
            this.port = port;
        }
    }

    public static final SessionJoin NO_JOIN = new SessionJoin() {
        @Override
        public JsonElement writeExpression(String locationKey, long version) {
            return null;
        }

        @Override
        public List<WriteRow> writes(String locationKey) {
            return Collections.<WriteRow>emptyList();
        }

        @Override
        public List<ReadRow> reads(String locationKey) {
            return Collections.<ReadRow>emptyList();
        }

        @Override
        public Set<String> mintedReadSymbols(long version) {
            return Collections.<String>emptySet();
        }

        @Override
        public Set<String> readSymbols(String locationKey, long version) {
            return Collections.<String>emptySet();
        }

        @Override
        public boolean moves(String symbol) {
            return false;
        }

        @Override
        public boolean repaired(String locationKey, long readEvent) {
            return false;
        }

        @Override
        public boolean concurrent(OccurrenceAddress reader,
                                  OccurrenceAddress writer) {
            return false;
        }
    };

    public static SessionJoin repairing(final SessionJoin join,
                                        final BiPredicate<String, Long> repaired,
                                        final BiPredicate<OccurrenceAddress,
                                                OccurrenceAddress> concurrent) {
        return new SessionJoin() {
            @Override
            public JsonElement writeExpression(String locationKey,
                                               long version) {
                return join.writeExpression(locationKey, version);
            }

            @Override
            public WriteRow write(String locationKey, long version) {
                return join.write(locationKey, version);
            }

            @Override
            public List<WriteRow> writes(String locationKey) {
                return join.writes(locationKey);
            }

            @Override
            public List<ReadRow> reads(String locationKey) {
                return join.reads(locationKey);
            }

            @Override
            public Set<String> mintedReadSymbols(long version) {
                return join.mintedReadSymbols(version);
            }

            @Override
            public Set<String> readSymbols(String locationKey, long version) {
                return join.readSymbols(locationKey, version);
            }

            @Override
            public boolean moves(String symbol) {
                return join.moves(symbol);
            }

            @Override
            public boolean repaired(String locationKey, long readEvent) {
                return repaired.test(locationKey, readEvent)
                        || join.repaired(locationKey, readEvent);
            }

            @Override
            public boolean concurrent(OccurrenceAddress reader,
                                      OccurrenceAddress writer) {
                return concurrent.test(reader, writer);
            }

            @Override
            public RefusalFrame frame(String occurrenceId) {
                return join.frame(occurrenceId);
            }

            @Override
            public RefusalFrame frameOfWrite(String locationKey,
                                             long version) {
                return join.frameOfWrite(locationKey, version);
            }

            @Override
            public ViewLeaf viewLeaf(String symbol) {
                return join.viewLeaf(symbol);
            }

            @Override
            public String viewLeafAt(String viewKey, long version,
                                     String port) {
                return join.viewLeafAt(viewKey, version, port);
            }
        };
    }

    public static String readKey(String locationKey, long readEvent) {
        return locationKey + "#e" + readEvent;
    }

    public static String mintedReadSymbol(SessionJoin join, long version) {
        if (version < 0L) return "";
        Set<String> symbols = join.mintedReadSymbols(version);
        if (symbols.isEmpty()) return "";
        if (symbols.size() > 1) return null;
        return symbols.iterator().next();
    }

    private final SmtSymbolTable symbols = new SmtSymbolTable();
    private final Map<String, Declared> declarations =
            new LinkedHashMap<String, Declared>();
    private final List<Stated> assertions = new ArrayList<Stated>();
    private final Set<String> assertedOnce = new LinkedHashSet<String>();
    private final Set<String> usedSymbols = new LinkedHashSet<String>();
    private final Map<String, Map<Long, String>> recordedObjects =
            new LinkedHashMap<String, Map<Long, String>>();
    private final Map<String, String> opaqueIdentities =
            new LinkedHashMap<String, String>();
    private final Map<String, SharedTerm> sharedTerms =
            new HashMap<String, SharedTerm>();
    private final Map<String, String> unsupportedDetail =
            new LinkedHashMap<String, String>();
    private final Set<String> pins = new LinkedHashSet<String>();
    private final Set<String> framedLeaves = new LinkedHashSet<String>();
    private final Set<String> movable = new LinkedHashSet<String>();
    private final Map<String, Map<Long, Candidate>> candidates =
            new HashMap<String, Map<Long, Candidate>>();
    private final Map<String, Map<String, WriteRow>> storeStates =
            new HashMap<String, Map<String, WriteRow>>();
    private final Map<String, Set<ReadRow>> askedThrough =
            new HashMap<String, Set<ReadRow>>();
    private final Set<String> nestedSelectors = new LinkedHashSet<String>();
    private final Deque<ReadAt> answering = new ArrayDeque<ReadAt>();
    private final Set<String> integralDomains = new LinkedHashSet<String>();

    private final boolean symbolsDeclareThemselves;
    private final ExpressionTable table;

    private Raised open;
    private String scope = "";
    private String arm = "";
    private Map<String, Map<String, Long>> clockBases =
            Collections.emptyMap();
    private SessionJoin join = NO_JOIN;
    private ExpressionTable openTable;
    private final Deque<Frame> frames = new ArrayDeque<Frame>();
    private Map<MemoKey, Attempt<?>> memo = new HashMap<MemoKey, Attempt<?>>();

    private void forget() {
        memo = new HashMap<MemoKey, Attempt<?>>();
        views = new HashMap<String, Attempt<Term>>();
    }
    private final Set<MemoKey> lowering = new HashSet<MemoKey>();
    private Set<JsonElement> still = identities();
    private Map<JsonElement, Boolean> statedBases = statedBases();
    private final List<Raised> raising = new ArrayList<Raised>();
    private final Raised root = new Raised();

    public SmtLowering(Map<String, Sort> declaredSymbols) {
        this(declaredSymbols, false, null);
    }

    private SmtLowering(Map<String, Sort> declaredSymbols,
                        boolean symbolsDeclareThemselves,
                        ExpressionTable table) {
        if (declaredSymbols != null) {
            for (Map.Entry<String, Sort> stated
                    : declaredSymbols.entrySet()) {
                if (stated.getKey() == null || stated.getValue() == null) {
                    continue;
                }
                this.declarations.put(stated.getKey(),
                        new Declared(stated.getValue(), true, false));
            }
        }
        this.symbolsDeclareThemselves = symbolsDeclareThemselves;
        this.table = table == null ? ExpressionTable.empty() : table;
    }

    private static final class Declared {
        private final Sort sort;
        private final boolean stated;
        private final boolean inQuery;

        private Declared(Sort sort, boolean stated, boolean inQuery) {
            this.sort = sort;
            this.stated = stated;
            this.inQuery = inQuery;
        }
    }

    public static SmtLowering forSession(SessionReader session,
                                         SessionJoin join) {
        SmtLowering lowering = new SmtLowering(
                Collections.<String, Sort>emptyMap(), true,
                session.expressions());
        lowering.scope = session.sessionId();
        lowering.join = repairing(join,
                (location, event) -> !join.writes(location).isEmpty(),
                join::concurrent);
        return lowering;
    }

    public static SessionJoin joinOf(final SessionReader session) {
        final VersionMap<WriteRow> writes = new VersionMap<WriteRow>();
        final Map<String, List<WriteRow>> byLocation =
                new HashMap<String, List<WriteRow>>();
        for (WriteRow write : session.writes()) {
            String key = locationKey(write.location());
            writes.put(key, write.version(), write);
            byLocation.computeIfAbsent(key, held -> new ArrayList<WriteRow>())
                    .add(write);
        }
        final Map<String, List<ReadRow>> readsOf =
                new HashMap<String, List<ReadRow>>();
        final Map<Long, Set<String>> minted =
                new HashMap<Long, Set<String>>();
        final VersionMap<Set<String>> observed =
                new VersionMap<Set<String>>();
        final Set<String> moving = new OpenSet<String>();
        for (RootMintRow root : session.roots()) moving.add(root.symbol());
        for (AttachRow attach : session.attaches()) {
            moving.add(attach.symbol());
        }
        for (DecisionRow decision : session.decisions()) {
            moving.addAll(decision.clockReadings().keySet());
        }
        for (ReadRow read : session.reads()) {
            if (read == null) continue;
            readsOf.computeIfAbsent(locationKey(read.location()),
                    held -> new ArrayList<ReadRow>()).add(read);
            if (read.symbol() == null || read.symbol().isEmpty()) continue;
            if (read.mintVersion() >= 0L) {
                add(minted, read.mintVersion(), read.symbol());
            } else if (read.observedVersion() >= 0L) {
                observed.computeIfAbsent(locationKey(read.location()),
                        read.observedVersion(),
                        key -> new LinkedHashSet<String>())
                        .add(read.symbol());
            }
        }
        minted.replaceAll((version, symbols) -> FrozenSet.of(symbols));
        observed.replaceAll(FrozenSet::of);
        Held.trimmed(byLocation);
        Held.trimmed(readsOf);
        final Map<String, ViewLeaf> viewLeaves =
                new HashMap<String, ViewLeaf>();
        final Map<String, String> leafAt = new HashMap<String, String>();
        for (AttachRow attach : session.attaches()) {
            ViewLeaf leaf = viewLeafOf(attach);
            if (leaf == null) continue;
            viewLeaves.put(attach.symbol(), leaf);
            leafAt.putIfAbsent(leaf.viewKey + "#" + leaf.version + "#"
                    + leaf.port, attach.symbol());
        }
        final Map<String, RefusalFrame> frames = frames(session);
        final VersionMap<RefusalFrame> framedWrites =
                new VersionMap<RefusalFrame>();
        for (WriteRow write : session.writes()) {
            RefusalFrame frame = write.initial() ? null
                    : frames.get(write.endpoint().occurrence().id());
            if (frame != null) {
                framedWrites.put(locationKey(write.location()),
                        write.version(), frame);
            }
        }
        return new SessionJoin() {
            @Override
            public JsonElement writeExpression(String locationKey,
                                               long version) {
                WriteRow write = writes.get(locationKey, version);
                return write == null ? null : session.expressions()
                        .expression(write.expressionRef());
            }

            @Override
            public WriteRow write(String locationKey, long version) {
                return writes.get(locationKey, version);
            }

            @Override
            public List<WriteRow> writes(String locationKey) {
                List<WriteRow> held = byLocation.get(locationKey);
                return held == null ? Collections.<WriteRow>emptyList()
                        : held;
            }

            @Override
            public List<ReadRow> reads(String locationKey) {
                List<ReadRow> held = readsOf.get(locationKey);
                return held == null ? Collections.<ReadRow>emptyList()
                        : held;
            }

            @Override
            public Set<String> mintedReadSymbols(long version) {
                Set<String> symbols =
                        minted.get(Long.valueOf(version));
                return symbols == null
                        ? Collections.<String>emptySet() : symbols;
            }

            @Override
            public Set<String> readSymbols(String locationKey, long version) {
                Set<String> symbols = observed.get(locationKey, version);
                return symbols == null
                        ? Collections.<String>emptySet() : symbols;
            }

            @Override
            public boolean moves(String symbol) {
                return moving.contains(symbol);
            }

            @Override
            public boolean repaired(String locationKey, long readEvent) {
                return false;
            }

            @Override
            public boolean concurrent(OccurrenceAddress reader,
                                      OccurrenceAddress writer) {
                return false;
            }

            @Override
            public RefusalFrame frame(String occurrenceId) {
                return frames.get(occurrenceId);
            }

            @Override
            public RefusalFrame frameOfWrite(String locationKey,
                                             long version) {
                return framedWrites.get(locationKey, version);
            }

            @Override
            public ViewLeaf viewLeaf(String symbol) {
                return viewLeaves.get(symbol);
            }

            @Override
            public String viewLeafAt(String viewKey, long version,
                                     String port) {
                return leafAt.get(viewKey + "#" + version + "#" + port);
            }
        };
    }

    static ViewLeaf viewLeafOf(AttachRow attach) {
        ContentPort.Parsed port = ContentPort.parse(
                attach.endpoint().site());
        String correlation = attach.correlationId();
        int at = correlation == null ? -1 : correlation.lastIndexOf('@');
        if (port == null || at < 0) return null;
        long version;
        try {
            version = Long.parseLong(correlation.substring(at + 1));
        } catch (NumberFormatException unversioned) {
            return null;
        }
        String node = attach.endpoint().occurrence().node().render();
        return new ViewLeaf(locationKey(LocationId.of(LocationKind.VIEW,
                port.transport + "@" + node, port.location)), version,
                attach.endpoint().site());
    }

    private static Map<String, RefusalFrame> frames(SessionReader session) {
        Map<Long, ExportRow> byHandle = new HashMap<Long, ExportRow>();
        for (ExportRow export : session.exports()) {
            byHandle.putIfAbsent(export.handle(), export);
        }
        Map<String, String> refusal = new LinkedHashMap<String, String>();
        Map<String, Set<String>> producers =
                new LinkedHashMap<String, Set<String>>();
        Map<String, List<JsonElement>> exports =
                new LinkedHashMap<String, List<JsonElement>>();
        for (GapRow gap : session.gaps(GapKind.UNSTATED_VALUE)) {
            String occurrence;
            try {
                occurrence = OccurrenceAddress.parse(gap.subject()).id();
            } catch (IllegalArgumentException noOccurrence) {
                continue;
            }
            refusal.putIfAbsent(occurrence, gap.detail());
            Set<String> named = producers.computeIfAbsent(occurrence,
                    key -> new LinkedHashSet<String>());
            List<JsonElement> held = exports.computeIfAbsent(occurrence,
                    key -> new ArrayList<JsonElement>());
            Matcher handle = REFUSED_HANDLE.matcher(gap.detail());
            ExportRow export = handle.find()
                    ? byHandle.get(Long.valueOf(handle.group(1))) : null;
            if (export == null) continue;
            named.add(export.endpoint().id());
            JsonElement expression = session.expressions().expression(
                    export.expressionRef());
            if (expression != null) held.add(expression);
        }
        Map<String, RefusalFrame> frames =
                new LinkedHashMap<String, RefusalFrame>();
        for (Map.Entry<String, String> each : refusal.entrySet()) {
            String occurrence = each.getKey();
            frames.put(occurrence, new RefusalFrame(String.join(", ",
                    producers.get(occurrence)), exports.get(occurrence),
                    each.getValue()));
        }
        return frames;
    }

    public Lowered lower(String expressionRef) {
        Attempt<Term> lowered = attempting(
                () -> reference(expressionRef, "lower:" + expressionRef));
        Term value = commit(lowered);
        if (value == null) {
            return Lowered.refused("ABSENT_EXPRESSION:" + expressionRef);
        }
        return new Lowered(value.text, value, lowered);
    }

    public Term term(String expressionRef, String origin) {
        return reference(expressionRef, origin);
    }

    public String statedTerm(String term, String origin) {
        if (term == null || term.isEmpty()) return "";
        String text = term;
        for (int round = 0; text.indexOf(REFERENCE) >= 0; round++) {
            if (round >= REFERENCE_ROUNDS) {
                refuse(UNSTATED + ":" + REFERENCE + "closure",
                        "an expression this term names lowers to text that "
                                + "names an expression reference again");
                return "";
            }
            String lowered = expand(text, origin);
            if (lowered.isEmpty()) return "";
            text = lowered;
        }
        return text;
    }

    private String expand(String term, String origin) {
        boolean[] refused = {false};
        String text = SmtNames.substitute(term, token -> {
            if (refused[0] || !SmtNames.reference(token)) return null;
            String lowered = loweredReference(token, origin);
            refused[0] = lowered.isEmpty();
            return refused[0] ? null : lowered;
        });
        return refused[0] ? "" : text;
    }

    private String loweredReference(String reference, String origin) {
        Term value = reference(reference, origin + ":" + reference);
        if (value == null) {
            refuse(UNSTATED + ":" + reference,
                    "a published term names this expression reference and "
                            + "the session's expression table does not "
                            + "hold it");
            return "";
        }
        return value.text;
    }

    private Term reference(String reference, String origin) {
        ExpressionTable expressions = openTable == null ? table : openTable;
        JsonObject expression = reference == null ? null
                : expressions.expression(reference);
        if (expression == null) return null;
        Term value = dispatch(expression, whole(expression, null), origin);
        sideCondition(value.precondition);
        return value;
    }

    static Sort whole(JsonElement value, Sort expected) {
        return named(value) && (expected == null
                || !expected.containerState()) ? Sort.REF : expected;
    }

    public static final class Lowered {
        private final String text;
        private final Term value;
        private final String refusal;
        private final List<String> dropped;

        private Lowered(String text, Term value, Attempt<?> lowered) {
            this.text = text;
            this.value = value;
            this.refusal = lowered.lowered() ? ""
                    : lowered.refusals().iterator().next();
            this.dropped = lowered.raised == null
                    ? Collections.<String>emptyList()
                    : new ArrayList<String>(lowered.raised.dropped);
        }

        private Lowered(String reason) {
            this.text = "";
            this.value = null;
            this.refusal = reason;
            this.dropped = Collections.<String>emptyList();
        }

        private static Lowered refused(String reason) {
            return new Lowered(reason);
        }

        public boolean ok() {
            return refusal.isEmpty() && !text.isEmpty() && dropped.isEmpty();
        }

        public String text() {
            return text;
        }

        public Term value() {
            return value;
        }

        @Override
        public String toString() {
            return ok() ? text : "refused:" + (refusal.isEmpty()
                    ? "joins dropped for a mint or a pin: " + dropped
                    : refusal);
        }
    }


    void clockBases(Map<String, Map<String, Long>> bases) {
        clockBases = bases == null
                ? Collections.<String, Map<String, Long>>emptyMap() : bases;
    }

    public void begin(String sessionId, SessionJoin sessionJoin,
                      ExpressionTable expressions) {
        frames.push(new Frame(open, scope, join, openTable, memo, still,
                statedBases, arm));
        this.open = new Raised();
        raising.add(open);
        this.scope = sessionId;
        this.join = sessionJoin;
        this.openTable = expressions;
        forget();
        this.still = identities();
        this.statedBases = statedBases();
    }

    private static Set<JsonElement> identities() {
        return Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>());
    }

    private static Map<JsonElement, Boolean> statedBases() {
        return new IdentityHashMap<JsonElement, Boolean>();
    }

    public List<String> end() {
        Raised closed = open;
        raising.remove(raising.size() - 1);
        Frame previous = frames.pop();
        open = previous.open;
        scope = previous.scope;
        join = previous.join;
        openTable = previous.table;
        memo = previous.memo;
        still = previous.still;
        statedBases = previous.statedBases;
        arm = previous.arm;
        top().gaps(closed);
        return closed.conditions.list();
    }

    private static final class Frame {
        private final Raised open;
        private final String scope;
        private final SessionJoin join;
        private final ExpressionTable table;
        private final Map<MemoKey, Attempt<?>> memo;
        private final Set<JsonElement> still;
        private final Map<JsonElement, Boolean> statedBases;
        private final String arm;

        private Frame(Raised open, String scope, SessionJoin join,
                      ExpressionTable table, Map<MemoKey, Attempt<?>> memo,
                      Set<JsonElement> still,
                      Map<JsonElement, Boolean> statedBases, String arm) {
            this.open = open;
            this.scope = scope;
            this.join = join;
            this.table = table;
            this.memo = memo;
            this.still = still;
            this.statedBases = statedBases;
            this.arm = arm;
        }
    }

    private final class Raised {
        private final Set<String> refusals = new LinkedHashSet<String>();
        private final Conditions conditions = new Conditions();
        private final Set<String> dropped = new LinkedHashSet<String>();
        private final Set<String> cuts = new LinkedHashSet<String>();
        private final Map<String, String> sortConflicts =
                new LinkedHashMap<String, String>();
        private final Map<String, String> pinnedReturns =
                new LinkedHashMap<String, String>();
        private final List<Unbound> unbound = new ArrayList<Unbound>();
        private final Set<Unbound> unboundHeld = Collections.newSetFromMap(
                new IdentityHashMap<Unbound, Boolean>());

        private void unbound(Unbound value) {
            if (unboundHeld.add(value)) unbound.add(value);
        }
        private final Map<String, Set<String>> viewLowered =
                new LinkedHashMap<String, Set<String>>();

        private void viewLowered(String symbol, String choice) {
            if (viewCases > 0) {
                viewLowered.computeIfAbsent(symbol,
                        unused -> new LinkedHashSet<String>()).add(choice);
            } else if (choice.isEmpty()) {
                viewDirect.add(symbol);
            } else {
                viewGuards.computeIfAbsent(symbol,
                        unused -> new LinkedHashSet<String>()).add(choice);
            }
        }

        private void under(String choice) {
            for (Set<String> choices : viewLowered.values()) {
                if (choices.remove("")) choices.add(choice);
            }
        }
        private final Map<String, String> diagnostics =
                new LinkedHashMap<String, String>();

        private void refusal(String subject) {
            if (this != root) refusals.add(subject);
        }

        private void condition(String predicate) {
            if (this == root) {
                assertPlain(predicate);
            } else {
                conditions.add(predicate);
            }
        }

        private void all(Raised other) {
            for (String subject : other.refusals) refusal(subject);
            if (this != root) {
                dropped.addAll(other.dropped);
                conditions.add(other.conditions);
            } else {
                for (String predicate : other.conditions.list()) {
                    assertPlain(predicate);
                }
            }
            gaps(other);
        }

        private void gaps(Raised other) {
            cuts.addAll(other.cuts);
            sortConflicts.putAll(other.sortConflicts);
            pinnedReturns.putAll(other.pinnedReturns);
            for (Unbound value : other.unbound) unbound(value);
            diagnostics.putAll(other.diagnostics);
            for (Map.Entry<String, Set<String>> symbol
                    : other.viewLowered.entrySet()) {
                for (String choice : symbol.getValue()) {
                    viewLowered(symbol.getKey(), choice);
                }
            }
        }
    }

    static final class Conditions {
        private List<Object> parts;

        void add(String predicate) {
            part(predicate);
        }

        void add(Conditions committed) {
            if (committed.parts != null) part(committed);
        }

        private void part(Object part) {
            if (parts == null) parts = new ArrayList<Object>(2);
            parts.add(part);
        }

        void clear() {
            parts = null;
        }

        List<String> list() {
            Set<String> read = new LinkedHashSet<String>();
            Set<Conditions> walked = Collections.newSetFromMap(
                    new IdentityHashMap<Conditions, Boolean>());
            Deque<Iterator<Object>> open = new ArrayDeque<Iterator<Object>>();
            walked.add(this);
            if (parts != null) open.push(parts.iterator());
            while (!open.isEmpty()) {
                Iterator<Object> at = open.peek();
                if (!at.hasNext()) {
                    open.pop();
                    continue;
                }
                Object part = at.next();
                if (part instanceof String) {
                    read.add((String) part);
                    continue;
                }
                Conditions inner = (Conditions) part;
                if (walked.add(inner) && inner.parts != null) {
                    open.push(inner.parts.iterator());
                }
            }
            return new ArrayList<String>(read);
        }
    }

    private Raised top() {
        int top = raising.size() - 1;
        if (top < 0) return root;
        Raised held = raising.get(top);
        if (held == null) {
            held = new Raised();
            raising.set(top, held);
        }
        return held;
    }

    private static final class MemoKey {
        private final JsonElement node;
        private final Object expected;

        private MemoKey(JsonElement node, Object expected) {
            this.node = node;
            this.expected = expected;
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof MemoKey)) return false;
            MemoKey key = (MemoKey) other;
            return node == key.node && expected == key.expected;
        }

        @Override
        public int hashCode() {
            return 31 * System.identityHashCode(node)
                    + System.identityHashCode(expected);
        }
    }

    private static final class Attempt<T> {
        private final T value;
        private final Raised raised;

        private Attempt(T value, Raised raised) {
            this.value = value;
            this.raised = raised;
        }

        public T value() {
            return value;
        }

        public boolean lowered() {
            return raised == null || raised.refusals.isEmpty();
        }

        private Set<String> refusals() {
            return raised == null ? Collections.<String>emptySet()
                    : raised.refusals;
        }
    }

    private <T> Attempt<T> attempting(Supplier<T> lowering) {
        raising.add(null);
        T value;
        Raised raised;
        try {
            value = lowering.get();
        } finally {
            raised = raising.remove(raising.size() - 1);
        }
        return new Attempt<T>(value, raised);
    }

    private <T> T commit(Attempt<T> attempt) {
        if (attempt.raised != null) top().all(attempt.raised);
        return attempt.value;
    }

    @SuppressWarnings("unchecked")
    private <T> T memoized(JsonElement node, Object expected,
                           Supplier<T> lowering, Supplier<T> cycle) {
        if (node == null || !node.isJsonObject()) return lowering.get();
        MemoKey key = new MemoKey(node, expected);
        Attempt<?> held = memo.get(key);
        if (held == null) {
            if (!this.lowering.add(key)) return cycle.get();
            try {
                held = attempting(lowering);
            } finally {
                this.lowering.remove(key);
            }
            memo.put(key, held);
        }
        return (T) commit(held);
    }

    private static final String LOWERING_CYCLE = "LoweringCycle";

    private void cycle(String origin) {
        refuse(LOWERING_CYCLE + ":" + origin, "this value was reached again "
                + "inside its own lowering, through a candidate's field or "
                + "a state asked by identity whose write rests on it: it was "
                + "read before that write, which therefore answers nothing "
                + "here");
    }

    public void arm(String selector) {
        arm = selector;
    }

    public int unboundMark() {
        return top().unbound.size();
    }

    public void unboundRollback(int mark) {
        Raised frame = top();
        List<Unbound> taken = frame.unbound.subList(
                Math.min(mark, frame.unbound.size()), frame.unbound.size());
        frame.unboundHeld.removeAll(taken);
        taken.clear();
    }

    public List<String> openRefusals() {
        return open == null ? Collections.<String>emptyList()
                : new ArrayList<String>(open.refusals);
    }


    private Term refuse(Reason reason, String origin, String detail,
                        Sort sort) {
        refuse(reason.composedSubject(origin, detail), "");
        return free(sort, IntegralWidth.NONE);
    }

    private static Term dependent(Term result, Term... inputs) {
        List<String> values = new ArrayList<String>();
        values.add(result.precondition);
        for (Term input : inputs) values.add(input.precondition);
        return result.withPrecondition(and(values));
    }

    private static Term definedResult(String text, Sort sort,
                                      IntegralWidth width,
                                      String definedness, Term... inputs) {
        return dependent(Term.of(text, sort, width, "", "", definedness),
                inputs);
    }

    private static Term result(String text, Sort sort, Term... inputs) {
        return definedResult(text, sort, IntegralWidth.NONE, "true", inputs);
    }

    private static Term result(String text, Sort sort, IntegralWidth width,
                               Term... inputs) {
        return definedResult(text, sort, width, "true", inputs);
    }

    private static Term shortCircuit(String text, Term left, Term right,
                                     boolean conjunction) {
        String rightEvaluated = conjunction ? left.text
                : "(not " + left.text + ")";
        return Term.of(text, Sort.BOOL).withPrecondition(
                and(Arrays.asList(left.precondition,
                        "(=> " + rightEvaluated + " " + right.precondition
                                + ")")));
    }

    private static String stringDefinedness(List<Term> dereferenced,
                                            List<Term> evaluated) {
        List<String> values = new ArrayList<String>();
        for (Term value : dereferenced) {
            values.add(value.precondition);
            values.add(stringNonNull(value));
        }
        for (Term value : evaluated) {
            values.add(value.precondition);
        }
        return and(values);
    }

    private static boolean nullnessUnknown(List<Term> dereferenced) {
        for (Term value : dereferenced) {
            if (value.sort == Sort.STRING && value.stringNullness.isEmpty()) {
                return true;
            }
        }
        return false;
    }

    private void assertJavaIntegralDomain(String term, String javaType) {
        JavaPrimitiveSmtSemantics.IntegralDomain domain =
                JavaPrimitiveSmtSemantics.domainOfJavaType(javaType);
        if (term.isEmpty() || domain == null || !integralDomains.add(term)) {
            return;
        }
        assertPlain(VmTermLowering.integralRange(domain.lower, term,
                domain.upper));
    }

    private void recordedReading(Term value, JsonElement observed,
                                 String origin) {
        Term recorded = dispatch(observed, value.sort,
                origin + ":recorded-reading");
        if (recorded.sort != value.sort) {
            refuse("RECORDED_READING_SORT:" + origin,
                    "the value this read observed does not lower to the "
                            + "sort the read itself has");
            return;
        }
        sideCondition("(= " + value.text + " " + recorded.text + ")");
    }


    private Term symbolTerm(JsonObject expression, Sort expected) {
        String raw = primitiveString(expression, "_exp");
        top().viewLowered(raw, "");
        if (VmExpressionIr.SYMBOLIC_NULL.equals(raw)) {
            return nullLeaf(expected);
        }
        if (VmExpressionIr.SYMBOLIC_VOID.equals(raw)) {
            return Term.of("true", Sort.BOOL);
        }
        String javaType = primitiveString(expression, "_java_type");
        Term viewed = throughView(raw, javaType, expected);
        if (viewed != null) return viewed;
        Sort sort = expected == Sort.REF
                && (VmRows.referencedObjectRid(raw) > 0L
                || VmRows.placedObject(raw))
                ? Sort.REF : leafSort(javaType, expected);
        if (sort == null) sort = Sort.REF;
        Declared held = declarations.get(raw);
        if (held != null && held.stated) {
            declareStated(raw, held.sort);
            usedSymbols.add(raw);
            return Term.of(raw, held.sort,
                    JavaPrimitiveSmtSemantics.widthOfJavaType(javaType),
                    "", "", "true");
        }
        if (expression.has(CALL) || METHOD_RETURN.matcher(raw).matches()) {
            return methodReturn(expression, raw, javaType, sort);
        }
        if (sort == Sort.REF || sort == Sort.MAP
                || sort == Sort.ARRAY_VALUE) {
            return Term.of(opaque(raw, sort), sort);
        }
        if (symbolsDeclareThemselves) {
            declare(raw, sort);
            usedSymbols.add(raw);
            return Term.of(raw, sort,
                    JavaPrimitiveSmtSemantics.widthOfJavaType(javaType),
                    "", "", "true");
        }
        return cut("UndeclaredFreeSymbol:" + raw,
                "no root mint, clock reading, attach or read row of this "
                        + "corpus states this symbol", sort, javaType);
    }

    private final List<String> viewing = new ArrayList<String>();
    private Map<String, Attempt<Term>> views =
            new HashMap<String, Attempt<Term>>();
    private int viewCycles;
    private int viewCases;
    private final Map<String, Set<String>> viewGuards =
            new LinkedHashMap<String, Set<String>>();
    private final Set<String> viewDirect = new HashSet<String>();
    private final Map<String, String> viewGuardNames =
            new LinkedHashMap<String, String>();

    public Map<String, Set<String>> viewGuarded() {
        Map<String, Set<String>> guarded =
                new LinkedHashMap<String, Set<String>>();
        for (Map.Entry<String, Set<String>> symbol : viewGuards.entrySet()) {
            if (!viewDirect.contains(symbol.getKey())) {
                guarded.put(symbol.getKey(), symbol.getValue());
            }
        }
        return guarded;
    }

    public String viewGuardName(String guard) {
        String named = viewGuardNames.get(guard);
        return named == null ? guard : named;
    }

    private Term throughView(String raw, String javaType, Sort expected) {
        ViewLeaf leaf = join.viewLeaf(raw);
        if (leaf == null) return null;
        int at = viewing.lastIndexOf(leaf.viewKey);
        if (at >= 0) {
            if (at < viewing.size() - 1) viewCycles++;
            return null;
        }
        String key = raw + SEPARATOR + javaType + SEPARATOR + expected;
        Attempt<Term> held = views.get(key);
        if (held != null) return commit(held);
        int cycles = viewCycles;
        Attempt<Term> answer = attempting(() -> viewed(leaf, raw, javaType,
                expected));
        if (viewCycles == cycles) views.put(key, answer);
        return commit(answer);
    }

    private Term viewed(ViewLeaf leaf, String raw, String javaType,
                        Sort expected) {
        viewing.add(leaf.viewKey);
        try {
            ReadRow view = null;
            for (ReadRow read : join.reads(leaf.viewKey)) {
                if (read.observedVersion() == leaf.version
                        && (movable.contains(scope + SEPARATOR
                        + readKey(leaf.viewKey, read.seq()))
                        || join.repaired(leaf.viewKey, read.seq()))) {
                    view = read;
                    break;
                }
            }
            if (view == null) return null;
            Term own = symbolTerm(symbolNode(raw, javaType), expected);
            Map<String, String> others = new LinkedHashMap<String, String>();
            for (WriteRow write : join.writes(leaf.viewKey)) {
                String version = Long.toString(write.version());
                String other = write.version() == leaf.version
                        || others.containsKey(version) ? null
                        : join.viewLeafAt(leaf.viewKey, write.version(),
                        leaf.port);
                if (other != null) others.put(version, other);
            }
            if (others.isEmpty()) return own;
            Term owner = symbolTerm(symbolNode(view.symbol(), "J"),
                    Sort.INT);
            Map<String, Term> answers = new LinkedHashMap<String, Term>();
            answers.put(Long.toString(leaf.version), own);
            for (Map.Entry<String, String> case_ : others.entrySet()) {
                String version = case_.getKey();
                String other = case_.getValue();
                String choice = "(= " + owner.text + " " + version + ")";
                viewGuardNames.putIfAbsent(choice, "version " + version
                        + " of " + leaf.viewKey + " (" + choice + ")");
                Attempt<Term> lowered;
                viewCases++;
                try {
                    lowered = attempting(() -> symbolTerm(
                            symbolNode(other, javaType), expected));
                } finally {
                    viewCases--;
                }
                if (lowered.raised != null) lowered.raised.under(choice);
                Term answer = commit(lowered);
                if (answer.sort == own.sort) answers.put(version, answer);
            }
            if (answers.size() < 2) return own;
            String value = perCandidate(owner.text, answers);
            String nullness = "false";
            for (Term answer : answers.values()) {
                if (!"false".equals(answer.stringNullness)) nullness = "";
            }
            return Term.of(shared("view_leaf__", own.sort, value), own.sort,
                    own.integralWidth, nullness, "", "true");
        } finally {
            viewing.remove(viewing.size() - 1);
        }
    }

    private static final Pattern METHOD_RETURN =
            Pattern.compile("M_[A-Z]_return[0-9]+");
    private static final String CALL = "call";

    private Term methodReturn(JsonObject expression, String raw,
                              String javaType, Sort sort) {
        JsonElement stated = expression.get(CALL);
        if (stated == null || !stated.isJsonObject()) {
            return cut("MethodReturnCallUnstated:" + raw, "the VM states no "
                    + "call for this method-return symbol (a VM before "
                    + "f14), so what its value was computed from is not "
                    + "known", sort, javaType);
        }
        JsonObject call = stated.getAsJsonObject();
        Term related = knownCall(optionalString(call, "holder") + " "
                + optionalString(call, "name"), array(call, "arguments"),
                "call:" + raw);
        if (related != null) return related;
        Set<String> moving = movers(call, true);
        if (!moving.isEmpty()) {
            freed("call:" + raw, "a call no relation states, over what "
                    + "can move", moving);
            return leaf(sort, javaType);
        }
        String returned = ReadRow.returned(expression);
        Term value = statedValue(returned, javaType);
        if (value == null) {
            return cut("UndeclaredFreeSymbol:" + raw, "the call that "
                    + "returned this symbol is no relation this lowering "
                    + "knows, and its node states no value it returned",
                    sort, javaType);
        }
        String name = symbols.mint("returned__", scope + SEPARATOR + raw, 10);
        if (!declared(name)) {
            declare(name, value.sort);
            String pin = "(= " + name + " " + value.text + ")";
            if (symbolsDeclareThemselves) {
                assertPlain(pin);
            } else {
                assertNamed("pinned_" + name, pin);
            }
        }
        top().pinnedReturns.put(raw, returned);
        return value.sort == Sort.STRING ? Term.nonNullString(name, "true")
                : Term.of(name, value.sort, value.integralWidth);
    }

    private ContainerSmtCodec.Term answered(JsonObject query) {
        String returned = ReadRow.returned(query);
        String javaType = primitiveString(query, "_java_type");
        long id = optionalLongInteger(query, ContainerSmtCodec.ANSWER, 0L);
        if (returned == null || id <= 0L || moves(query)) return null;
        Term value = statedValue(returned, javaType);
        if (value == null) return null;
        String name = symbols.mint("answer__", scope + SEPARATOR + id, 10);
        if (!declared(name)) {
            declare(name, value.sort);
            String pin = "(= " + name + " " + value.text + ")";
            if (symbolsDeclareThemselves) {
                assertPlain(pin);
            } else {
                assertNamed("pinned_" + name, pin);
            }
        }
        String kind = primitiveString(query, "shape") + ":"
                + primitiveString(query, "operation");
        top().diagnostics.put("ContainerAnswerPinned:" + kind + "@" + scope,
                "a " + kind + " over a chain with no stated base answers "
                        + "what its call returned, pinned by a named "
                        + "assertion where nothing it rests on moves");
        ContainerSmtCodec.Sort sort = VmTermLowering.containerSortOf(
                value.sort);
        return value.sort == Sort.STRING
                ? ContainerSmtCodec.Term.string(name, "false")
                : new ContainerSmtCodec.Term(name, sort, value.integralWidth);
    }

    private ContainerSmtCodec.Term unknown(JsonObject cell) {
        long id = optionalLongInteger(cell, ContainerSmtCodec.ANSWER, 0L);
        if (id <= 0L) {
            refuse("ContainerRelation:UNKNOWN:unnamed", "");
            return null;
        }
        String name = symbols.mint("unknown__", scope + SEPARATOR + id, 10);
        if (!declared(name)) declare(name, Sort.VALUE);
        top().diagnostics.put("ContainerCellUnknown@" + scope, "a cell a "
                + "callback the run never ran would have stored is free on "
                + "the arm the run did not take (CONTAINER_PINNED)");
        return new ContainerSmtCodec.Term(name, ContainerSmtCodec.Sort.VALUE);
    }

    private Term knownCall(String callee, JsonArray arguments,
                           String origin) {
        if (RENDERINGS.contains(callee) && arguments.size() == 1) {
            return javaToString(arguments, origin);
        }
        if (ENUM_VALUE_OF.equals(callee)) return enumName(arguments, origin);
        if (ENUM_ORDINAL.equals(callee)) {
            return enumOrdinal(arguments, origin);
        }
        boolean integer = "java/lang/Integer parseInt".equals(callee);
        if (!integer && !"java/lang/Long parseLong".equals(callee)) {
            return null;
        }
        Sort sort = Sort.INT;
        if (arguments.size() == 2 && !"10".equals(constantPayload(
                primitiveString(arguments.get(1).isJsonObject()
                        ? arguments.get(1).getAsJsonObject()
                        : new JsonObject(), "_exp")))) {
            return refuse(Reason.MODEL_SEMANTICS_MISSING, origin,
                    callee + ":RADIX_NOT_10", sort);
        }
        if (arguments.size() != 1 && arguments.size() != 2) {
            return refuse(Reason.MODEL_SEMANTICS_MISSING, origin,
                    callee + ":ARITY", sort);
        }
        IntegralWidth width = integer ? IntegralWidth.JAVA_INT
                : IntegralWidth.JAVA_LONG;
        JsonElement rendered = StringIdentities.parsedOperand(integer,
                arguments.get(0));
        if (rendered != null) {
            Term value = dispatch(rendered, null, origin + ":rendered");
            if (value.sort == Sort.INT) {
                return dependent(Term.of(value.text, Sort.INT, width), value);
            }
        }
        Term text = dispatch(arguments.get(0), null, origin + ":string");
        if (text.sort != Sort.STRING
                || nullnessUnknown(Collections.singletonList(text))) {
            return refuse(Reason.MODEL_SEMANTICS_MISSING, origin,
                    callee + ":STRING_UNSTATED", sort);
        }
        String string = text.text;
        String digits = "(str.to_int (ite (or (str.prefixof \"-\" " + string
                + ") (str.prefixof \"+\" " + string + ")) (str.substr "
                + string + " 1 (- (str.len " + string + ") 1)) " + string
                + "))";
        String value = "(ite (str.prefixof \"-\" " + string + ") (- "
                + digits + ") " + digits + ")";
        JavaPrimitiveSmtSemantics.IntegralDomain domain =
                JavaPrimitiveSmtSemantics.domainOfJavaType(integer ? "I" : "J");
        return definedResult(value, sort, width,
                and(Arrays.asList(stringDefinedness(
                        Collections.singletonList(text),
                        Collections.<Term>emptyList()),
                        "(<= 0 " + digits + ")",
                        VmTermLowering.integralRange(domain.lower, value,
                                domain.upper))));
    }

    private static final String ENUM_VALUE_OF = "java/lang/Enum valueOf";
    private static final String ENUM_ORDINAL = "java/lang/Enum ordinal";

    private Term enumName(JsonArray arguments, String origin) {
        EnumChoice choice = enumChoice(arguments, origin);
        return choice == null ? refuse(Reason.MODEL_SEMANTICS_MISSING, origin,
                ENUM_VALUE_OF + ":NAME_UNSTATED", Sort.STRING)
                : choice.constant(choice.names);
    }

    private Term enumOperand(JsonElement operand, String origin) {
        JsonObject chosen = enumRead(operand);
        if (chosen == null) return dispatch(operand, null, origin);
        return "MethodExpression".equals(VmExpressionIr.typeOf(chosen))
                ? enumName(array(chosen, "_param_list"), origin)
                : dispatch(chosen, null, origin);
    }

    private Term enumOrdinal(JsonArray arguments, String origin) {
        Term name = arguments.size() < 2 ? null
                : enumOperand(arguments.get(0), origin + ":constant");
        List<String> names = enumNames(arguments, 1);
        if (name == null || name.sort != Sort.STRING || names == null) {
            return refuse(Reason.MODEL_SEMANTICS_MISSING, origin,
                    ENUM_ORDINAL + ":CONSTANT_UNSTATED", Sort.INT);
        }
        String ordinal = "(- 1)";
        for (int index = names.size() - 1; index >= 0; index--) {
            ordinal = "(ite (= " + name.text + " "
                    + VmExpressionIr.quote(names.get(index))
                    + ") " + index + " " + ordinal + ")";
        }
        return definedResult(ordinal, Sort.INT, IntegralWidth.JAVA_INT,
                "true", name);
    }

    private final class EnumChoice {
        final List<String> names;
        final List<String> chosen;
        final Term operand;

        EnumChoice(List<String> names, List<String> chosen, Term operand) {
            this.names = names;
            this.chosen = chosen;
            this.operand = operand;
        }

        Term constant(List<String> spelled) {
            String value = VmExpressionIr.quote(
                    spelled.get(spelled.size() - 1));
            for (int index = spelled.size() - 2; index >= 0; index--) {
                value = "(ite " + chosen.get(index) + " "
                        + VmExpressionIr.quote(spelled.get(index)) + " "
                        + value + ")";
            }
            return definedResult(value, Sort.STRING, IntegralWidth.NONE,
                    and(Arrays.asList(stringNonNull(operand), or(chosen))),
                    operand);
        }
    }

    private EnumChoice enumChoice(JsonArray arguments, String origin) {
        List<String> names = arguments.size() < 3 ? null
                : enumNames(arguments, 2);
        if (names == null) return null;
        JsonElement name = arguments.get(1);
        Boolean upper = caseConversion(name);
        Term operand = dispatch(upper == null ? name
                : name.getAsJsonObject().getAsJsonArray("_param_list").get(0),
                null, origin + ":name");
        if (operand.sort != Sort.STRING
                || nullnessUnknown(Collections.singletonList(operand))) {
            return null;
        }
        List<String> chosen = new ArrayList<String>();
        for (String constant : names) {
            chosen.add(upper == null ? "(= " + operand.text + " "
                    + VmExpressionIr.quote(constant) + ")"
                    : converts(operand.text, constant, upper));
        }
        return new EnumChoice(names, chosen, operand);
    }

    private static Boolean caseConversion(JsonElement name) {
        if (name == null || !name.isJsonObject()
                || !VmExpressionIr.STRING_OPERATION_TYPE.equals(
                        VmExpressionIr.typeOf(name))) {
            return null;
        }
        String operation = optionalString(name.getAsJsonObject(), "_name");
        return "toUpperCase".equals(operation) ? Boolean.TRUE
                : "toLowerCase".equals(operation) ? Boolean.FALSE : null;
    }

    private static String converts(String operand, String target,
                                   boolean upper) {
        List<String> letters = new ArrayList<String>();
        letters.add("(= (str.len " + operand + ") " + target.length() + ")");
        for (int index = 0; index < target.length(); index++) {
            char wanted = target.charAt(index);
            boolean cased = upper ? Character.isLowerCase(wanted)
                    : Character.isUpperCase(wanted);
            if (wanted > 127 || cased) return "false";
            List<String> any = new ArrayList<String>();
            for (char from : new LinkedHashSet<Character>(Arrays.asList(
                    wanted, Character.toLowerCase(wanted),
                    Character.toUpperCase(wanted)))) {
                if ((upper ? Character.toUpperCase(from)
                        : Character.toLowerCase(from)) == wanted) {
                    any.add("(= (str.at " + operand + " " + index + ") "
                            + VmExpressionIr.quote(String.valueOf(from)) + ")");
                }
            }
            letters.add(or(any));
        }
        return and(letters);
    }

    private Term convertedConstant(JsonArray params, boolean upper,
                                   String origin) {
        JsonElement receiver = params.size() == 0 ? null : params.get(0);
        while (receiver != null && VmExpressionIr.consumerBoundary(receiver)) {
            receiver = receiver.getAsJsonObject().get(
                    VmExpressionIr.EXPRESSION);
        }
        if (receiver == null || !receiver.isJsonObject()
                || !"MethodExpression".equals(VmExpressionIr.typeOf(receiver))
                || !ENUM_VALUE_OF.equals(optionalString(
                        receiver.getAsJsonObject(), "_name"))) {
            return null;
        }
        EnumChoice choice = enumChoice(array(receiver.getAsJsonObject(),
                "_param_list"), origin + ":constant");
        if (choice == null) return null;
        List<String> spelled = new ArrayList<String>();
        for (String name : choice.names) {
            spelled.add(upper ? name.toUpperCase(java.util.Locale.ROOT)
                    : name.toLowerCase(java.util.Locale.ROOT));
        }
        return choice.constant(spelled);
    }

    private JsonObject enumRead(JsonElement operand) {
        JsonElement at = operand;
        boolean read = false;
        for (int hop = 0; at != null && at.isJsonObject() && hop < 8;
             hop++) {
            JsonObject node = at.getAsJsonObject();
            if (VmExpressionIr.consumerBoundary(node)) {
                at = node.get(VmExpressionIr.EXPRESSION);
                continue;
            }
            String type = VmExpressionIr.typeOf(node);
            if ("MethodExpression".equals(type)) {
                return read && ENUM_VALUE_OF.equals(optionalString(node,
                        "_name")) ? node : null;
            }
            if ("ConStringSymbolExp".equals(type)) {
                return read && stringLiteral(node) != null ? node : null;
            }
            if (!VmRows.GUARDED_READ_TYPE.equals(type)
                    || !unstatedVersion(node)) {
                return null;
            }
            read = true;
            at = observedVersionExpression(node);
        }
        return null;
    }

    private boolean unstatedVersion(JsonObject read) {
        String key = locationKey(JsonFields.object(read, "location"));
        long version = VmRows.joinedVersion(read);
        if (key.isEmpty() || version < 0L) return true;
        JsonElement written = join.writeExpression(key, version);
        return (written == null || written.isJsonNull())
                && join.frameOfWrite(key, version) == null
                && "".equals(mintedReadSymbol(join, version))
                && !join.repaired(key, VmRows.readEvent(read));
    }

    private static List<String> enumNames(JsonArray arguments, int from) {
        List<String> names = new ArrayList<String>();
        for (int index = from; index < arguments.size(); index++) {
            String name = stringLiteral(arguments.get(index));
            if (name == null) return null;
            names.add(name);
        }
        return names.isEmpty() ? null : names;
    }

    private static final Set<String> RENDERINGS = new LinkedHashSet<String>(
            Arrays.asList("java/lang/String valueOf",
                    "java/lang/Integer toString", "java/lang/Long toString"));

    private Term nullLeaf(Sort expected) {
        if (expected == Sort.VALUE) {
            return Term.of(ContainerStateModel.NULL_CELL, Sort.VALUE);
        }
        if (expected != null && expected.containerState()) {
            return unstated("NullComparedToContainerState:" + expected,
                    "a container state is the contents this replay "
                            + "propagated, and nothing states whether the "
                            + "reference holding it was null", expected, "");
        }
        return Term.of("nullRef", Sort.REF);
    }

    interface Binder<T> {
        Term join(JsonElement value);

        T joined(Term value);

        T minted(String symbol);

        T pinned();

        default T own() {
            return null;
        }

        String returned();

        T free();

        default T framed() {
            return free();
        }

        T refused(Term joined, String subject, String detail);
    }

    <T> T bind(String key, long version, long event, JsonElement projected,
               Binder<T> binder) {
        Attempt<Term> joined = null;
        Set<String> cut = new LinkedHashSet<String>();
        boolean unwritten = true;
        if (!key.isEmpty() && version >= 0L) {
            JsonElement written = join.writeExpression(key, version);
            RefusalFrame frame = join.frameOfWrite(key, version);
            Set<String> frameMoving = frame == null
                    ? Collections.<String>emptySet() : frameMovers(frame);
            if (!frameMoving.isEmpty()) {
                freed(key + "@" + version, "written on an arrival its "
                        + "occurrence refused, from " + frame.producer,
                        frameMoving);
                return binder.framed();
            }
            if (written != null && !written.isJsonNull()) {
                unwritten = false;
                JsonElement value = projected != null
                        && !projected.isJsonNull() ? projected : written;
                joined = attempting(() -> binder.join(value));
                if (joined.lowered()) return binder.joined(commit(joined));
                if (join.repaired(key, event)) {
                    cut.add("read " + key + "@" + version);
                }
                cut.addAll(movers(value, true));
                cut.addAll(movers(written, true));
            }
            String minted = mintedReadSymbol(join, version);
            if (minted == null) {
                return binder.refused(joined == null ? null
                                : commit(joined), "MintVersion:" + key + "@"
                                + version + ":" + join.mintedReadSymbols(
                                version),
                        "two placeholder rows of this session state mint "
                                + "version " + version + " under different "
                                + "symbols: " + join.mintedReadSymbols(
                                version) + ", so what the read it made "
                                + "returned has no answer");
            }
            if (!minted.isEmpty()) {
                if (joined != null) top().dropped.add(joined.value().text);
                return binder.minted(minted);
            }
        }
        if (!cut.isEmpty()) {
            top().dropped.add(joined.value().text);
            freed(key + "@" + version, "its write did not lower and rests "
                    + "on what can move", cut);
            return binder.free();
        }
        if (unwritten && version >= 0L && !key.isEmpty()
                && join.repaired(key, event)) {
            T own = binder.own();
            if (own != null) return own;
        }
        T pinned = binder.pinned();
        if (pinned != null) {
            if (joined != null) top().dropped.add(joined.value().text);
            if (unwritten) {
                held(key + "@" + version, binder.returned() == null ? ""
                        : binder.returned(),
                        "no write row states this version");
            }
            return pinned;
        }
        return binder.refused(joined == null ? null : commit(joined),
                "Read:" + key + "@" + version, (joined == null
                        ? "no write of this location at this version in "
                        + "this session"
                        : "the write of this version did not lower (its "
                        + "refusal is stated beside this)")
                        + ", and the recording states no value the read "
                        + "returned");
    }

    private void freed(String subject, String why, Set<String> movesWith) {
        top().unbound(new Unbound(Unbound.FREE, subject, "", why,
                new ArrayList<String>(movesWith), arm));
    }

    public List<String> ownConditions(Supplier<Boolean> binding) {
        Attempt<Boolean> held = attempting(binding);
        List<String> own = new ArrayList<String>();
        if (held.raised != null && Boolean.TRUE.equals(held.value)) {
            own.addAll(held.raised.conditions.list());
            held.raised.conditions.clear();
        }
        commit(held);
        return own;
    }

    private boolean moves(JsonElement expression) {
        return !movers(expression, false).isEmpty();
    }

    static final String HAVOC = "unsupported__";

    static boolean havocs(String text) {
        for (String name : SmtNames.names(text)) {
            if (name.startsWith(HAVOC)) return true;
        }
        return false;
    }

    public Set<String> movers(String term) {
        Set<String> found = new LinkedHashSet<String>();
        for (String name : SmtNames.names(term)) {
            if (SmtNames.reference(name)) {
                found.addAll(movers(new JsonPrimitive(name), true));
            } else if (join.moves(name)) {
                found.add(name);
            }
        }
        return found;
    }

    private Set<String> movers(JsonElement expression, boolean all) {
        Set<String> found = new LinkedHashSet<String>();
        if (expression == null || expression.isJsonNull()) return found;
        ExpressionTable expressions = openTable == null ? table : openTable;
        Set<JsonElement> walked = Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>());
        List<JsonElement> pending = new ArrayList<JsonElement>();
        pending.add(expression);
        while (!pending.isEmpty()) {
            JsonElement node = pending.remove(pending.size() - 1);
            if (node == null || node.isJsonNull()) continue;
            if (node.isJsonPrimitive()) {
                String text = node.getAsString();
                if (text.startsWith(REFERENCE)) {
                    pending.add(expressions.expression(text));
                }
                continue;
            }
            if (still.contains(node) || !walked.add(node)) continue;
            if (node.isJsonArray()) {
                for (JsonElement child : node.getAsJsonArray()) {
                    pending.add(child);
                }
                continue;
            }
            JsonObject object = node.getAsJsonObject();
            String type = primitiveString(object, "_type");
            String symbol = primitiveString(object, "_exp");
            if (VmExpressionIr.SYMBOL_TYPE.equals(type)
                    && join.moves(symbol)) {
                found.add(symbol);
                if (!all) return found;
            }
            if (VmRows.GUARDED_READ_TYPE.equals(type)) {
                String key = locationKey(JsonFields.object(object,
                        "location"));
                long version = VmRows.joinedVersion(object);
                if (join.repaired(key, VmRows.readEvent(object))) {
                    found.add("read " + key + "@" + version);
                    if (!all) return found;
                }
                for (String minted : join.mintedReadSymbols(version)) {
                    if (join.moves(minted)) {
                        found.add(minted);
                        if (!all) return found;
                    }
                }
                pending.add(join.writeExpression(key, version));
            }
            pending.addAll(object.asMap().values());
        }
        if (found.isEmpty()) still.addAll(walked);
        return found;
    }

    private Term guardedReadTerm(JsonObject expression, Sort expected,
                                 String origin) {
        JsonObject location = JsonFields.object(expression, "location");
        String key = locationKey(location);
        long version = VmRows.joinedVersion(expression);
        String javaType = primitiveString(expression, "_java_type");
        long event = VmRows.readEvent(expression);
        return bind(key, version, event,
                observedVersionExpression(expression), new Binder<Term>() {
            @Override
            public Term join(JsonElement value) {
                answering.push(new ReadAt(key, version));
                try {
                    JsonElement asked = movedQuery(value, key, version,
                            event);
                    return element(dispatch(asked, whole(asked, expected),
                            origin + ":join"), expression, location, key,
                            version, expected);
                } finally {
                    answering.pop();
                }
            }

            @Override
            public Term joined(Term value) {
                String read = rowSymbol(key, version, value.sort);
                return read == null ? value
                        : symbolTerm(symbolNode(read, javaType), expected);
            }

            @Override
            public Term minted(String symbol) {
                return symbolTerm(symbolNode(symbol, javaType), expected);
            }

            @Override
            public Term pinned() {
                String pinned = pinnedSymbol(key, version);
                return pinned != null
                        ? symbolTerm(symbolNode(pinned, javaType), expected)
                        : statedValue(returned(), javaType);
            }

            @Override
            public Term own() {
                Set<String> named = join.readSymbols(key, version);
                Term value = statedValue(returned(), javaType);
                if (named.size() != 1 || value == null) return null;
                String read = named.iterator().next();
                declareStated(read, value.sort);
                return symbolTerm(symbolNode(read, javaType), expected);
            }

            @Override
            public String returned() {
                return ReadRow.returned(expression);
            }

            @Override
            public Term free() {
                return leaf(expected, javaType);
            }

            @Override
            public Term framed() {
                Term leaf = leaf(expected, javaType);
                framedLeaves.add(leaf.text);
                return leaf;
            }

            @Override
            public Term refused(Term joined, String subject, String detail) {
                if (joined == null) {
                    return unstated(subject, detail, expected, javaType);
                }
                refuse(UNSTATED + ":" + subject, detail);
                return joined;
            }
        });
    }

    private JsonElement movedQuery(JsonElement projected, String key,
                                   long version, long event) {
        if (!join.repaired(key, event) || !ContainerSmtCodec.handles(
                projected)) {
            return projected;
        }
        JsonObject relation = projected.getAsJsonObject();
        JsonElement receiver = relation.get("receiver");
        if (VIEWS.contains(optionalString(relation, "operation"))
                || ContainerSmtCodec.handles(receiver) && VIEWS.contains(
                optionalString(receiver.getAsJsonObject(), "operation"))) {
            return projected;
        }
        Set<String> named = join.readSymbols(key, version);
        if (named.size() != 1) return projected;
        String symbol = named.iterator().next();
        Declared held = declarations.get(symbol);
        if (held == null || !held.stated || !held.sort.containerState()) {
            return projected;
        }
        JsonObject state = symbolNode(symbol, "");
        state.add(MOVED_CHAIN, join.writeExpression(key, version));
        return asOf(relation, state);
    }

    private static final String MOVED_CHAIN = "inSessionObservedChain";

    private String rowSymbol(String key, long version, Sort sort) {
        if (sort.containerState()) return null;
        Set<String> named = join.readSymbols(key, version);
        if (named.size() != 1) return null;
        String read = named.iterator().next();
        Declared held = declarations.get(read);
        return held != null && held.stated && held.sort == sort
                && !pins.contains(scope + SEPARATOR + read) ? read : null;
    }

    private String pinnedSymbol(String key, long version) {
        Set<String> named = join.readSymbols(key, version);
        if (named.size() != 1) return null;
        String read = named.iterator().next();
        return pins.contains(scope + SEPARATOR + read) ? read : null;
    }

    public void pin(String symbol, Sort sort) {
        declareStated(symbol, sort);
        if (pins.add(scope + SEPARATOR + symbol)) {
            forget();
        }
    }

    public void path() {
        movable.clear();
        nestedSelectors.clear();
        forget();
        viewGuards.clear();
        viewDirect.clear();
        viewGuardNames.clear();
        unstatedDropped();
    }

    private void unstatedDropped() {
        Deque<SharedTerm> reaching = new ArrayDeque<SharedTerm>();
        for (Stated held : assertions) {
            if (held.reached) continue;
            held.reached = true;
            kept(SmtNames.names(held.formula), reaching);
        }
        for (String cell : cellOf.values()) {
            kept(SmtNames.names(cell), reaching);
        }
        while (!reaching.isEmpty()) kept(reaching.pop().names(), reaching);
        for (Iterator<SharedTerm> each = sharedTerms.values().iterator();
             each.hasNext();) {
            SharedTerm term = each.next();
            if (term.kept) continue;
            each.remove();
            symbols.forget(term.name);
        }
    }

    private void kept(Iterable<String> names, Deque<SharedTerm> reaching) {
        for (String name : names) {
            SharedTerm term = sharedTerms.get(name);
            if (term != null && !term.kept) {
                term.kept = true;
                reaching.push(term);
            }
        }
    }

    public void movable(ReadRow read) {
        if (movable.add(scope + SEPARATOR + readKey(
                locationKey(read.location()), read.seq()))) {
            forget();
        }
    }

    private static JsonObject symbolNode(String symbol, String javaType) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "SymbolExpression");
        node.addProperty("_exp", symbol);
        node.addProperty("_java_type", javaType == null ? "" : javaType);
        return node;
    }

    Term statedValue(String concreteValue, String javaType) {
        String text = concreteValue == null ? "" : concreteValue.trim();
        if (text.isEmpty()) return null;
        String string = smtLiteral(text, Sort.STRING);
        if (!string.isEmpty()) return Term.nonNullString(string, "true");
        if (VmExpressionIr.SYMBOLIC_NULL.equals(text)
                || VmRows.referencedObjectRid(text) > 0L) {
            return symbolTerm(symbolNode(text, javaType), Sort.REF);
        }
        Sort sort = JavaSmtSorts.sortOfJava(javaType);
        String literal = smtLiteral(text, sort);
        if (literal.isEmpty()) return null;
        return Term.of(literal, sort,
                JavaPrimitiveSmtSemantics.widthOfJavaType(javaType));
    }

    private Term element(Term value, JsonObject expression,
                         JsonObject location, String key, long version,
                         Sort expected) {
        if (!value.sort.containerState()) return value;
        String javaType = primitiveString(expression, "_java_type");
        Sort cell = JavaSmtSorts.sortOfJava(javaType);
        if (cell.containerState() || cell == Sort.UNKNOWN
                || expected != null && expected.containerState()) {
            return value;
        }
        long slot = optionalLongInteger(location, "slot", -1L);
        boolean indexed = value.sort == Sort.ARRAY_VALUE && slot >= 0L
                && locationKind(primitiveString(location, "locationKind"))
                == LocationKind.ARRAY;
        if (indexed) {
            Term cellValue = Term.of("(indexed_read " + value.text + " "
                    + slot + ")", Sort.VALUE);
            Term unboxed = fromValue(cellValue, javaType);
            if (unboxed != null && !unboxed.sort.containerState()) {
                return dependent(unboxed, value);
            }
        }
        return unstated("ContainerElement:" + key
                        + "@" + version + ":" + value.sort + "!=" + cell,
                "the write this read joined to states the whole container "
                        + "at that version, and this location does not say "
                        + "which cell of it the read returned", cell,
                javaType);
    }

    private Term containerTerm(JsonObject expression, boolean field,
                               String origin) {
        ContainerSmtCodec.Term value = field
                ? ContainerSmtCodec.field(expression, host(origin))
                : ContainerSmtCodec.term(expression, host(origin));
        if (value == null) {
            String named = primitiveString(expression, "operation");
            if (named.isEmpty()) {
                named = field
                        ? "FIELD:" + primitiveString(expression, "ownerClass")
                        + "@" + optionalLongInteger(expression,
                        "fieldOffset", -1L)
                        : primitiveString(expression, "shape");
            }
            refuse("ContainerRelation:" + (named.isEmpty() ? "unnamed"
                    : named), "");
            return leaf(null, primitiveString(expression, "_java_type"));
        }
        Sort sort = VmTermLowering.sortOfContainer(value.sort);
        if (sort == Sort.UNKNOWN) {
            refuse(origin + ":CONTAINER_STATE_USED_AS_VALUE", "");
            return free(Sort.VALUE, IntegralWidth.NONE);
        }
        return lowered(value);
    }

    private static Term lowered(ContainerSmtCodec.Term value) {
        Sort sort = VmTermLowering.sortOfContainer(value.sort);
        return value.nullness.isEmpty()
                ? Term.vm(value.text, sort, value.integralWidth)
                : Term.of(value.text, sort, value.integralWidth,
                value.nullness, "", "true");
    }


    private static final String CANDIDATE_UNANSWERED = "CANDIDATE_UNANSWERED";

    private ContainerSmtCodec.Term projection(JsonObject access,
                                              ContainerSmtCodec.Term cell,
                                              String origin) {
        ReadRow read = movableOwner(access);
        if (read == null) return cell;
        String key = locationKey(read.location());
        Term asked = symbolTerm(symbolNode(read.symbol(), "L"), Sort.REF);
        String ownerClass = optionalString(access, "ownerClass");
        JsonObject own = asked.sort == Sort.REF
                ? ownObject(access, ownerClass) : null;
        if (own == null) {
            refuse(UNSTATED + ":OwnerCandidates:" + key, "a STATE family "
                    + "may re-point this owner, and neither its sort nor "
                    + "the projection's pair names an object, so no case of "
                    + "it is the run's own");
            return cell;
        }
        Sort sort = VmTermLowering.sortOfContainer(cell.sort);
        Map<String, Term> answers = new LinkedHashMap<String, Term>();
        answers.put(symbolTerm(own, Sort.REF).text, lowered(cell));
        long run = VmRows.referencedObjectRid(primitiveString(own, "_exp"));
        String slot = Long.toString(optionalLongInteger(access,
                "fieldOffset", -1L));
        for (Map.Entry<Long, Candidate> each
                : candidates(key, ownerClass).entrySet()) {
            if (each.getKey() == run) continue;
            Term field = fieldOf(each.getKey(), slot, each.getValue(), sort,
                    key, origin);
            if (field != null) {
                answers.put(symbolTerm(each.getValue().spelling, Sort.REF)
                        .text, field);
            }
        }
        return perCandidateTerm(asked.text, answers, cell);
    }

    private static final String OWNER = "owner";
    private static final String CONCRETE_VALUE = "concreteValue";

    private ReadRow movableOwner(JsonObject node) {
        JsonElement found = node.get(OWNER);
        while (VmExpressionIr.consumerBoundary(found)) {
            found = found.getAsJsonObject().get(VmExpressionIr.EXPRESSION);
        }
        if (!VmRows.GUARDED_READ_TYPE.equals(VmExpressionIr.typeOf(found))) {
            return null;
        }
        JsonObject read = found.getAsJsonObject();
        String key = locationKey(JsonFields.object(read, "location"));
        long event = VmRows.readEvent(read);
        if (!movable.contains(scope + SEPARATOR + readKey(key, event))) {
            return null;
        }
        for (ReadRow row : join.reads(key)) {
            if (row.seq() == event) return row;
        }
        return null;
    }

    private String perCandidate(String owner, Map<String, Term> answers) {
        List<Map.Entry<String, Term>> cases =
                new ArrayList<Map.Entry<String, Term>>(answers.entrySet());
        List<String> defined = new ArrayList<String>();
        String value = "";
        for (int index = cases.size() - 1; index >= 0; index--) {
            String is = "(= " + owner + " " + cases.get(index).getKey() + ")";
            Term answer = cases.get(index).getValue();
            value = value.isEmpty() ? answer.text
                    : "(ite " + is + " " + answer.text + " " + value + ")";
            defined.add(0, and(Arrays.asList(is, answer.precondition)));
        }
        sideCondition(VmTermLowering.or(defined));
        return value;
    }

    private ContainerSmtCodec.Term perCandidateTerm(
            String owner, Map<String, Term> answers,
            ContainerSmtCodec.Term run) {
        String value = perCandidate(owner, answers);
        if (run.sort != ContainerSmtCodec.Sort.STRING) {
            return new ContainerSmtCodec.Term(value, run.sort,
                    run.integralWidth);
        }
        List<Map.Entry<String, Term>> cases =
                new ArrayList<Map.Entry<String, Term>>(answers.entrySet());
        String nullness = "";
        boolean nonNull = true;
        for (int index = cases.size() - 1; index >= 0; index--) {
            Term answer = cases.get(index).getValue();
            if (answer.stringNullness.isEmpty()) {
                return ContainerSmtCodec.Term.string(value, "");
            }
            nonNull &= "false".equals(answer.stringNullness);
            nullness = nullness.isEmpty() ? answer.stringNullness
                    : "(ite (= " + owner + " " + cases.get(index).getKey()
                    + ") " + answer.stringNullness + " " + nullness + ")";
        }
        return ContainerSmtCodec.Term.string(value,
                nonNull ? "false" : nullness);
    }

    private static ContainerSmtCodec.Term codecTerm(Term value) {
        return value.sort == Sort.STRING
                ? ContainerSmtCodec.Term.string(value.text,
                value.stringNullness)
                : new ContainerSmtCodec.Term(value.text,
                VmTermLowering.containerSortOf(value.sort),
                value.integralWidth);
    }

    private static JsonObject ownObject(JsonObject access,
                                        String ownerClass) {
        JsonElement value = access.get(CONCRETE_VALUE);
        while (VmExpressionIr.consumerBoundary(value)) {
            value = value.getAsJsonObject().get(VmExpressionIr.EXPRESSION);
        }
        if (VmRows.GUARDED_READ_TYPE.equals(VmExpressionIr.typeOf(value))) {
            JsonObject cell = JsonFields.object(value.getAsJsonObject(),
                    "location");
            long rid = optionalLongInteger(cell, "ownerSymRid", -1L);
            if (rid > 0L && optionalLongInteger(cell, "slot", -1L)
                    == optionalLongInteger(access, "fieldOffset", -2L)) {
                return symbolNode("M_L'" + ownerClass + "'_" + rid,
                        ownerClass);
            }
        }
        JsonElement owner = access.get("concreteOwner");
        return VmExpressionIr.SYMBOL_TYPE.equals(VmExpressionIr.typeOf(owner))
                && VmRows.referencedObjectRid(primitiveString(
                owner.getAsJsonObject(), "_exp")) > 0L
                ? owner.getAsJsonObject() : null;
    }

    private static final class Candidate {
        private final JsonObject spelling;
        private final long firstStored;
        private final List<WriteRow> stores;

        private Candidate(JsonObject spelling, long firstStored,
                          List<WriteRow> stores) {
            this.spelling = spelling;
            this.firstStored = firstStored;
            this.stores = stores;
        }
    }

    private Map<Long, Candidate> candidates(String key, String ownerClass) {
        return candidates.computeIfAbsent(scope + SEPARATOR + key
                + SEPARATOR + ownerClass, unused -> {
            String spelled = ownerClass == null ? "M_L'"
                    : "M_L'" + ownerClass + "'_";
            Map<Long, JsonObject> spellings =
                    new LinkedHashMap<Long, JsonObject>();
            Map<Long, Long> first = new HashMap<Long, Long>();
            Map<Long, List<WriteRow>> stored =
                    new HashMap<Long, List<WriteRow>>();
            Set<JsonElement> walked = ExpressionWalk.identitySet();
            List<WriteRow> stores = new ArrayList<WriteRow>(join.writes(key));
            stores.sort(Comparator.comparingLong(WriteRow::seq));
            for (WriteRow store : stores) {
                JsonElement value = join.writeExpression(key,
                        store.version());
                if (named(value)) {
                    stored.computeIfAbsent(VmRows.referencedObjectRid(
                            primitiveString(value.getAsJsonObject(),
                                    "_exp")), rid -> new ArrayList<WriteRow>())
                            .add(store);
                }
                Deque<JsonElement> roots = new ArrayDeque<JsonElement>();
                roots.add(value);
                while (!roots.isEmpty()) {
                    for (ExpressionWalk walk = ExpressionWalk.of(roots.pop(),
                            walked); walk.hasNext(); ) {
                        JsonObject node = walk.next();
                        String raw = primitiveString(node, "_exp");
                        if (named(node) && raw.startsWith(spelled)) {
                            long rid = VmRows.referencedObjectRid(raw);
                            spellings.putIfAbsent(rid, node);
                            first.putIfAbsent(rid, store.seq());
                        } else if (VmRows.GUARDED_READ_TYPE.equals(
                                optionalString(node, "_type"))
                                && observedVersionExpression(node) == null) {
                            JsonElement written = join.writeExpression(
                                    locationKey(JsonFields.object(node,
                                            "location")),
                                    VmRows.joinedVersion(node));
                            if (written != null) roots.add(written);
                        }
                    }
                }
            }
            Map<Long, Candidate> found = new LinkedHashMap<Long, Candidate>();
            for (Map.Entry<Long, JsonObject> each : spellings.entrySet()) {
                found.put(each.getKey(), new Candidate(each.getValue(),
                        first.get(each.getKey()), stored.getOrDefault(
                        each.getKey(), Collections.<WriteRow>emptyList())));
            }
            return found;
        });
    }

    static boolean named(JsonElement node) {
        return VmExpressionIr.SYMBOL_TYPE.equals(VmExpressionIr.typeOf(node))
                && VmRows.referencedObjectRid(primitiveString(
                node.getAsJsonObject(), "_exp")) > 0L;
    }

    private Term fieldOf(long rid, String slot, Candidate candidate,
                         Sort sort, String owner, String origin) {
        String cell = locationKey(LocationId.of(LocationKind.INSTANCE,
                Long.toString(rid), slot));
        List<WriteRow> writes = join.writes(cell);
        Term field = null;
        String why;
        if (writes.isEmpty()) {
            field = unwritten(cell);
            why = "no write of it and no one value its reads state";
        } else if (writes.size() > 1) {
            why = writes.size() + " writes of it";
        } else if (writes.get(0).seq() >= candidate.firstStored) {
            why = "its one write only after " + owner + " stored the object";
        } else {
            Attempt<Term> written = attempting(() -> dispatch(
                    join.writeExpression(cell, writes.get(0).version()), sort,
                    origin + ":" + cell));
            if (written.lowered()) field = commit(written);
            why = "its one write, which does not lower to the " + sort
                    + " the projection reads" + (written.lowered() ? ""
                    : " (" + String.join(", ", written.refusals()) + ")");
        }
        if (field != null && field.sort == sort) return field;
        top().diagnostics.put(CANDIDATE_UNANSWERED + ":" + cell + "@"
                + scope, "a STATE family may re-point " + owner + " to this "
                + "object, and this session states " + why + ", so no "
                + "pairing that delivers it is composed");
        return null;
    }

    private Term unwritten(String cell) {
        Term stated = null;
        Set<Long> versions = new LinkedHashSet<Long>();
        for (ReadRow read : join.reads(cell)) {
            Term value = statedValue(read.concreteValue(), read.javaType());
            if (value == null
                    || stated != null && !stated.text.equals(value.text)) {
                return null;
            }
            stated = value;
            versions.add(read.observedVersion());
        }
        return versions.size() == 1 ? stated : null;
    }

    private static final String REFERENT_STATE_UNSTATED =
            "REFERENT_STATE_UNSTATED";
    private static final Set<String> VIEWS = new LinkedHashSet<String>(
            Arrays.asList("ITERATOR", "KEY_VIEW", "VALUE_VIEW", "ENTRY_VIEW",
                    "NEXT", "ENTRY"));

    private ContainerSmtCodec.Term query(JsonObject relation,
                                         ContainerSmtCodec.Term own,
                                         String origin) {
        ReadRow read = movableOwner(relation);
        if (read == null) return own;
        String key = locationKey(read.location());
        Term asked = symbolTerm(symbolNode(read.symbol(), "L"), Sort.REF);
        JsonObject self = asked.sort == Sort.REF ? identityRead(key, read)
                : null;
        if (self == null) {
            refuse(UNSTATED + ":OwnerCandidates:" + key, "a STATE family "
                    + "may re-point this owner, and it is no reference "
                    + "whose write or row names the object the run's read "
                    + "returned (a container's own read names none), so "
                    + "which objects it may be is not stated");
            return own;
        }
        askedThrough(read);
        Term run = lowered(own);
        long rid = VmRows.referencedObjectRid(primitiveString(self, "_exp"));
        Map<Long, Candidate> objects = candidates(key, null);
        Map<String, Term> answers = new LinkedHashMap<String, Term>();
        answers.put(symbolTerm(self, Sort.REF).text, objects.containsKey(rid)
                ? answerOf(relation, objects.get(rid), read, key, origin,
                run) : run);
        for (Map.Entry<Long, Candidate> each : objects.entrySet()) {
            Candidate candidate = each.getValue();
            if (each.getKey() == rid || candidate.stores.isEmpty()) continue;
            Term answer = answerOf(relation, candidate, read, key, origin,
                    null);
            if (answer != null) {
                answers.put(symbolTerm(candidate.spelling, Sort.REF).text,
                        answer);
            }
        }
        return perCandidateTerm(asked.text, answers, own);
    }

    private JsonObject identityRead(String key, ReadRow read) {
        JsonElement written = join.writeExpression(key,
                read.observedVersion());
        if (named(written)) return written.getAsJsonObject();
        return VmRows.referencedObjectRid(read.concreteValue()) > 0L
                ? symbolNode(read.concreteValue(), read.javaType()) : null;
    }

    private Term answerOf(JsonObject relation, Candidate candidate,
                          ReadRow read, String owner, String origin,
                          Term run) {
        String object = primitiveString(candidate.spelling, "_exp");
        Map<Long, String> selectors = new LinkedHashMap<Long, String>();
        Map<Long, Term> options = new LinkedHashMap<Long, Term>();
        for (WriteRow store : candidate.stores) {
            if (run != null && store.version() == read.observedVersion()) {
                continue;
            }
            Map<String, WriteRow> through = storeStates.computeIfAbsent(
                    scope + SEPARATOR + read.symbol() + SEPARATOR
                            + store.version(),
                    unused -> new LinkedHashMap<String, WriteRow>());
            String reason = store.referentStateRefused() != null
                    ? store.referentStateRefused()
                    : store.referentState() == null ? "NONE"
                    : join.writeExpression(locationKey(store.referentState()
                    .location()), store.referentState().version()) == null
                    ? "UNPUBLISHED" : "";
            if (reason.isEmpty()) {
                String state = locationKey(store.referentState().location());
                boolean answered = false;
                for (WriteRow version : statesOf(join.writes(state),
                        store.referentState(), read, join::concurrent)) {
                    String selector = selectors.computeIfAbsent(
                            version.version(), unused -> nested(read,
                                    object, version.version()));
                    through.putIfAbsent(selector, version);
                    if (!options.containsKey(version.version())) {
                        JsonElement chain = join.writeExpression(state,
                                version.version());
                        if (chain == null || !chain.isJsonObject()) continue;
                        Attempt<ContainerSmtCodec.Term> asked = attempting(
                                () -> ContainerSmtCodec.term(asOf(relation,
                                        chain.getAsJsonObject()),
                                        host(origin)));
                        if (!asked.lowered() || asked.value() == null) {
                            continue;
                        }
                        options.put(version.version(), conditioned(asked));
                    }
                    answered = true;
                }
                if (!answered) reason = "UNLOWERED";
            }
            if (!reason.isEmpty()) {
                top().diagnostics.put(REFERENT_STATE_UNSTATED + ":"
                        + reason + ":" + object + "@" + scope, "a STATE "
                        + "family may re-point " + owner + " to this object"
                        + " through a store at version " + store.version()
                        + ", and no state of it answers the query ("
                        + reason + "), so no pairing that delivers it "
                        + "through that store is composed");
            }
        }
        if (run == null && options.isEmpty()) return null;
        if (run != null && selectors.isEmpty()) return run;
        List<Long> versions = new ArrayList<Long>(options.keySet());
        Term last = run != null ? run
                : options.get(versions.get(versions.size() - 1));
        String value = last.text;
        List<String> held = new ArrayList<String>();
        for (int index = versions.size() - 1; index >= 0; index--) {
            Term answer = options.get(versions.get(index));
            String selector = selectors.get(versions.get(index));
            if (answer != last) {
                value = "(ite " + selector + " " + answer.text + " " + value
                        + ")";
            }
            held.add(0, run != null ? "(=> " + selector + " "
                    + answer.precondition + ")"
                    : and(Arrays.asList(selector, answer.precondition)));
        }
        List<String> required = new ArrayList<String>();
        for (Map.Entry<Long, String> selector : selectors.entrySet()) {
            if (!options.containsKey(selector.getKey())) {
                required.add("(not " + selector.getValue() + ")");
            }
        }
        List<String> all = new ArrayList<String>(selectors.values());
        if (run == null) {
            required.add(Arms.exactlyOne(all));
            required.add(VmTermLowering.or(held));
        } else {
            required.add(atMostOne(all));
            required.addAll(held);
        }
        return Term.vm(value, last.sort, last.integralWidth)
                .withPrecondition(and(required));
    }

    private static String atMostOne(List<String> selectors) {
        if (selectors.size() < 2) return "true";
        StringBuilder sum = new StringBuilder("(<= (+");
        for (String selector : selectors) {
            sum.append(" (ite ").append(selector).append(" 1 0)");
        }
        return sum.append(") 1)").toString();
    }

    private String nested(ReadRow read, String object, long version) {
        String selector = symbols.mint("nest__", scope + SEPARATOR
                + read.symbol() + SEPARATOR + object + SEPARATOR + version,
                12);
        declare(selector, Sort.BOOL);
        nestedSelectors.add(selector);
        return selector;
    }

    private void askedThrough(ReadRow owner) {
        Set<ReadRow> asked = askedThrough.computeIfAbsent(scope + SEPARATOR
                + owner.symbol(), unused -> new LinkedHashSet<ReadRow>());
        ReadAt at = answering.peek();
        if (at == null) return;
        for (ReadRow row : join.reads(at.key)) {
            if (row.location().kind() == LocationKind.MAP
                    && row.observedVersion() == at.version
                    && row.endpoint().occurrence().equals(
                    owner.endpoint().occurrence())) {
                asked.add(row);
            }
        }
    }

    public String storeChoice(String symbol, WriteRow store) {
        Map<String, WriteRow> through = storeStates.get(scope + SEPARATOR
                + symbol + SEPARATOR + store.version());
        return through == null ? ""
                : VmTermLowering.or(new ArrayList<String>(through.keySet()));
    }

    public List<StateChoice> stateChoices(String session, String symbol,
                                          WriteRow store) {
        Map<String, WriteRow> through = storeStates.get(session + SEPARATOR
                + symbol + SEPARATOR + store.version());
        if (through == null) return Collections.<StateChoice>emptyList();
        List<ReadRow> readers = new ArrayList<ReadRow>(
                askedThrough.getOrDefault(session + SEPARATOR + symbol,
                        Collections.<ReadRow>emptySet()));
        List<StateChoice> choices = new ArrayList<StateChoice>();
        for (Map.Entry<String, WriteRow> state : through.entrySet()) {
            choices.add(new StateChoice(state.getKey(), state.getValue(),
                    readers));
        }
        return choices;
    }

    public Set<String> nestedSelectors() {
        return Collections.unmodifiableSet(nestedSelectors);
    }

    public static final class StateChoice {
        public final String selector;
        public final WriteRow state;
        public final List<ReadRow> readers;

        StateChoice(String selector, WriteRow state, List<ReadRow> readers) {
            this.selector = selector;
            this.state = state;
            this.readers = Collections.unmodifiableList(readers);
        }
    }

    private static final class ReadAt {
        private final String key;
        private final long version;

        private ReadAt(String key, long version) {
            this.key = key;
            this.version = version;
        }
    }

    public static List<WriteRow> statesOf(
            List<WriteRow> writes, WriteRow.Referent state, ReadRow read,
            BiPredicate<OccurrenceAddress, OccurrenceAddress> concurrent) {
        List<WriteRow> versions = new ArrayList<WriteRow>();
        for (WriteRow version : writes) {
            if (version.version() >= state.version()) versions.add(version);
        }
        versions.sort(RowOrder::compare);
        if (versions.isEmpty()
                || versions.get(0).version() != state.version()) {
            return Collections.<WriteRow>emptyList();
        }
        int live = 0;
        while (live + 1 < versions.size() && RowOrder.beforeCut(
                versions.get(live + 1).seq(), versions.get(live + 1).tie(),
                read.seq(), read.tie())) {
            live++;
        }
        List<WriteRow> seen = new ArrayList<WriteRow>();
        seen.add(versions.get(live));
        for (WriteRow later : versions.subList(live + 1, versions.size())) {
            if (concurrent.test(read.endpoint().occurrence(),
                    later.endpoint().occurrence())) {
                seen.add(later);
            }
        }
        return seen;
    }

    static JsonObject asOf(JsonObject relation, JsonObject state) {
        JsonObject asked = JsonFields.shallowCopy(relation);
        asked.remove(OWNER);
        asked.remove(CONCRETE_VALUE);
        asked.remove(ContainerSmtCodec.ANSWER);
        JsonElement receiver = relation.get("receiver");
        asked.add("receiver", ContainerSmtCodec.handles(receiver)
                && VIEWS.contains(optionalString(receiver.getAsJsonObject(),
                "operation")) ? asOf(receiver.getAsJsonObject(), state)
                : state);
        return asked;
    }

    private Term conditioned(Attempt<ContainerSmtCodec.Term> asked) {
        List<String> required = new ArrayList<String>();
        if (asked.raised != null) {
            required.addAll(asked.raised.conditions.list());
            top().gaps(asked.raised);
        }
        return lowered(asked.value()).withPrecondition(and(required));
    }

    public Map<String, String> diagnostics() {
        return Collections.unmodifiableMap(root.diagnostics);
    }


    public String recordedValue(String raw, String smt) {
        for (Sort sort : Sort.values()) {
            if (sort == Sort.UNKNOWN || !sort.smt.equals(smt)) continue;
            String literal = VmTermLowering.smtLiteral(raw, sort);
            if (!literal.isEmpty() || sort != Sort.REF) return literal;
            return VmRows.referencedObjectRid(raw) > 0L
                    || VmRows.placedObject(raw) ? opaque(raw, sort) : "";
        }
        return "";
    }

    private String opaque(String raw, Sort sort) {
        String name = symbols.mint("identity__",
                scope + SEPARATOR + sort + SEPARATOR + (sort == Sort.REF
                        ? VmRows.objectIdentity(raw) : raw), 10);
        declare(name, sort);
        boolean minted = opaqueIdentities.put(name, raw) == null;
        long rid = VmRows.referencedObjectRid(raw);
        if (minted && sort == Sort.REF
                && (rid > 0L || VmRows.placedObject(raw))) {
            assertPlain("(not (= " + name + " nullRef))");
        }
        if (minted && sort == Sort.REF && rid > 0L) {
            recordedObjects.computeIfAbsent(scope,
                    session -> new LinkedHashMap<Long, String>())
                    .put(rid, name);
        }
        return name;
    }

    public String identityOf(String name) {
        return opaqueIdentities.get(name);
    }

    public void assertIdentitiesDistinct() {
        for (Map.Entry<String, Map<Long, String>> session
                : recordedObjects.entrySet()) {
            Map<Long, String> held = session.getValue();
            if (held.size() < 2) continue;
            assertNamed("identities_distinct__"
                            + ArtifactIO.digest(session.getKey(), 10),
                    "(distinct " + String.join(" ", held.values()) + ")");
        }
    }


    private static final Object CONTAINER_OPERAND = new Object();

    private ContainerSmtCodec.Host host(final String origin) {
        return new ContainerSmtCodec.Host() {
            @Override
            public ContainerSmtCodec.Term state(
                    JsonElement identity, ContainerSmtCodec.Sort shape) {
                Sort stateSort = shape == ContainerSmtCodec.Sort.INDEXED
                        ? Sort.ARRAY_VALUE : Sort.MAP;
                Term reference = named(identity) ? null : dispatch(identity,
                        Sort.REF, origin + ":container-state");
                if (reference == null || reference.sort != Sort.REF) {
                    if (identity != null && identity.isJsonObject()) {
                        String raw = primitiveString(
                                identity.getAsJsonObject(), "_exp");
                        if (!raw.isEmpty()) {
                            String name = symbols.mint("container__",
                                    scope + SEPARATOR + shape + SEPARATOR
                                            + raw, 10);
                            declare(name, stateSort);
                            return new ContainerSmtCodec.Term(name, shape);
                        }
                    }
                    unsupported("ContainerStateIdentity:" + shape);
                    return null;
                }
                String accessor = shape == ContainerSmtCodec.Sort.INDEXED
                        ? "indexed_state_of" : "assoc_state_of";
                return new ContainerSmtCodec.Term(
                        "(" + accessor + " " + reference.text + ")", shape);
            }

            @Override
            public ContainerSmtCodec.Term share(
                    ContainerSmtCodec.Term value) {
                return name(value);
            }

            @Override
            public ContainerSmtCodec.Term operand(
                    JsonElement expression,
                    ContainerSmtCodec.Sort expected) {
                Supplier<ContainerSmtCodec.Term> cycle = () -> {
                    cycle(origin);
                    return null;
                };
                if (ContainerSmtCodec.handles(expression)) {
                    return memoized(expression, CONTAINER_OPERAND,
                            () -> name(ContainerSmtCodec.term(
                                    expression.getAsJsonObject(), this)),
                            cycle);
                }
                if (ContainerSmtCodec.handlesField(expression)) {
                    return memoized(expression, CONTAINER_OPERAND,
                            () -> name(ContainerSmtCodec.field(
                                    expression.getAsJsonObject(), this)),
                            cycle);
                }
                Term value = dispatch(expression,
                        VmTermLowering.sortOfContainer(expected),
                        origin + ":container-operand");
                return codecTerm(value);
            }

            @Override
            public ContainerSmtCodec.Term box(JsonElement expression) {
                String javaType =
                        VmTermLowering.expressionJavaType(expression);
                Term value = dispatch(expression, JavaSmtSorts.sortOfJava(
                        javaType).containerState() ? Sort.REF : null,
                        origin + ":container-value");
                String cell = cellOf.get(value.text);
                String boxed = cell != null ? cell : boxed(value, javaType);
                if (boxed.isEmpty()) {
                    refuse(CUT + ":CannotBox:" + javaType,
                            "at " + origin + ": a container cell declared \""
                                    + javaType + "\" lowered to "
                                    + value.sort + ": "
                                    + value.text.substring(0, Math.min(160,
                                    value.text.length())));
                    return null;
                }
                return name(new ContainerSmtCodec.Term(boxed,
                        ContainerSmtCodec.Sort.VALUE));
            }

            @Override
            public ContainerSmtCodec.Term unbox(
                    ContainerSmtCodec.Term value, String javaType) {
                ContainerSmtCodec.Term unboxed = name(
                        ContainerStateModel.unboxValue(value, javaType,
                                VmTermLowering.unboxedCellSort(
                                        JavaSmtSorts.sortOfJava(javaType)),
                                this));
                if (unboxed != null && value != null
                        && unboxed.sort == ContainerSmtCodec.Sort.REF) {
                    cellOf.put(unboxed.text, value.text);
                }
                return unboxed;
            }

            @Override
            public ContainerSmtCodec.Term projection(
                    JsonObject access, ContainerSmtCodec.Term cell) {
                return SmtLowering.this.projection(access, cell, origin);
            }

            @Override
            public ContainerSmtCodec.Term query(
                    JsonObject relation, ContainerSmtCodec.Term answer) {
                return SmtLowering.this.query(relation, answer, origin);
            }

            @Override
            public JsonElement chain(JsonElement state) {
                JsonElement found = state;
                while (VmExpressionIr.consumerBoundary(found)) {
                    found = found.getAsJsonObject().get(
                            VmExpressionIr.EXPRESSION);
                }
                if (found != null && found.isJsonObject()
                        && found.getAsJsonObject().has(MOVED_CHAIN)) {
                    return found.getAsJsonObject().get(MOVED_CHAIN);
                }
                if (!VmRows.GUARDED_READ_TYPE.equals(
                        VmExpressionIr.typeOf(found))) {
                    return found;
                }
                JsonObject read = found.getAsJsonObject();
                return join.writeExpression(locationKey(JsonFields.object(
                        read, "location")), VmRows.joinedVersion(read));
            }

            @Override
            public ContainerSmtCodec.Term answered(JsonObject query) {
                return SmtLowering.this.answered(query);
            }

            @Override
            public ContainerSmtCodec.Term unknown(JsonObject cell) {
                return SmtLowering.this.unknown(cell);
            }

            @Override
            public Boolean statedBase(JsonElement node) {
                return statedBases.get(node);
            }

            @Override
            public void statedBase(JsonElement node, Boolean stated) {
                statedBases.put(node, stated);
            }

            @Override
            public void require(String predicate) {
                sideCondition(predicate);
            }

            @Override
            public void unsupported(String reason) {
                refuse(reason, "");
            }

            @Override
            public void diagnostic(String subject, String detail) {
                top().diagnostics.put(subject + "@" + scope, detail);
            }
        };
    }

    private static String boxed(Term value, String javaType) {
        String integral = ContainerStateModel.boxIntegral(value.text, javaType);
        if (integral.isEmpty()
                && value.integralWidth == IntegralWidth.JAVA_LONG) {
            integral = ContainerStateModel.boxIntegral(value.text, "J");
        }
        if (!integral.isEmpty()) return integral;
        switch (value.sort) {
            case BOOL: return "(VBool " + value.text + ")";
            case INT: return "(VInt " + value.text + ")";
            case FLOAT32: return "(VFloat " + value.text + ")";
            case FLOAT64: return "(VDouble " + value.text + ")";
            case STRING: return "(VString " + value.text + ")";
            case REF: return "(VRef " + value.text + ")";
            case VALUE: return value.text;
            default: return "";
        }
    }

    private final Map<String, String> cellOf = new HashMap<String, String>();

    private static final class SharedTerm {
        private final String name;
        private final Sort sort;
        private final String body;
        private volatile SmtNames.Named names;
        private boolean kept;

        private SharedTerm(String name, Sort sort, String body) {
            this.name = name;
            this.sort = sort;
            this.body = body;
        }

        private SmtNames.Named names() {
            SmtNames.Named read = names;
            if (read == null) {
                read = SmtNames.named(Collections.singletonList(body));
                names = read;
            }
            return read;
        }
    }

    private ContainerSmtCodec.Term name(ContainerSmtCodec.Term value) {
        if (value == null || value.text.isEmpty()
                || value.text.charAt(0) != '(') {
            return value;
        }
        Sort sort = VmTermLowering.sortOfContainer(value.sort);
        if (sort == Sort.UNKNOWN) return value;
        String name = shared("container_dag__", sort, value.text);
        return value.nullness.isEmpty() ? new ContainerSmtCodec.Term(
                name, value.sort, value.integralWidth, value.indexedSize)
                : ContainerSmtCodec.Term.string(name, value.nullness);
    }

    private String shared(String prefix, Sort sort, String text) {
        String name = symbols.mint(prefix,
                sort.name() + SEPARATOR + scoped(text), 24);
        if (!sharedTerms.containsKey(name)) {
            sharedTerms.put(name, new SharedTerm(name, sort, text));
        }
        return name;
    }


    private String scoped(String text) {
        if (text == null || text.isEmpty() || scope.isEmpty()) return text;
        return SmtNames.substitute(text, token -> usedSymbols.contains(token)
                ? scope + SEPARATOR + token : null);
    }

    public String leafEquals(String symbol, Sort symbolSort,
                             String symbolJavaType, Term delivered,
                             String sentJavaType) {
        Sort sent = delivered.sort;
        if (symbolSort == null || symbolSort == Sort.VALUE
                || symbolSort == sent) {
            return "(= " + symbol + " " + delivered.text + ")";
        }
        if (JavaSmtSorts.isChar(symbolJavaType)
                || JavaSmtSorts.isChar(sentJavaType)) {
            return null;
        }
        String d = delivered.text;
        if (symbolSort == Sort.BOOL && sent == Sort.STRING) {
            return "(= " + symbol + " (str.in_re " + d + " (re.++"
                    + " (re.union (str.to_re \"t\") (str.to_re \"T\"))"
                    + " (re.union (str.to_re \"r\") (str.to_re \"R\"))"
                    + " (re.union (str.to_re \"u\") (str.to_re \"U\"))"
                    + " (re.union (str.to_re \"e\") (str.to_re \"E\")))))";
        }
        if (symbolSort == Sort.STRING && sent == Sort.BOOL) {
            return "(= " + symbol + " (ite " + d + " \"true\" \"false\"))";
        }
        if (symbolSort == Sort.STRING && sent == Sort.INT) {
            return "(= " + symbol + " (java_int_to_string " + d + "))";
        }
        if (symbolSort == Sort.INT && sent == Sort.STRING) {
            String digits = "(str.substr " + d + " 1 (- (str.len " + d
                    + ") 1))";
            return "(and (str.in_re " + d + " (re.++ (re.opt (re.union"
                    + " (str.to_re \"+\") (str.to_re \"-\")))"
                    + " (re.+ (re.range \"0\" \"9\"))))"
                    + " (= " + symbol + " (ite (= (str.at " + d + " 0) \"-\")"
                    + " (- (str.to_int " + digits + "))"
                    + " (ite (= (str.at " + d + " 0) \"+\")"
                    + " (str.to_int " + digits + ") (str.to_int " + d
                    + ")))))";
        }
        return null;
    }

    public void leafRefused(String symbol, Sort parsed, Sort sent) {
        refuse(SORT_CONFLICT + ":" + symbol, unrelated(parsed, sent));
    }

    public void leafUnrelated(String symbol, Sort parsed, Sort sent) {
        top().diagnostics.put(SORT_CONFLICT + ":" + symbol + ":" + sent,
                unrelated(parsed, sent));
    }

    private static String unrelated(Sort parsed, Sort sent) {
        return "a run sent this leaf as " + sent + " and the read parsed it"
                + " as " + parsed + ", which no rendering relates";
    }

    public void declare(String name, Sort sort) {
        put(name, sort, false);
    }

    public void declareStated(String name, Sort sort) {
        put(name, sort, true);
    }

    public void state(String name, Sort sort) {
        Declared held = declarations.get(name);
        if (held != null && (held.stated || held.sort != sort)) return;
        declarations.put(name, new Declared(sort, true,
                held != null && held.inQuery));
        forget();
    }

    public boolean declareStated(String name) {
        Declared held = declarations.get(name);
        if (held == null || !held.stated) return false;
        put(name, held.sort, true);
        return true;
    }

    public Sort statedSort(String name) {
        Declared held = declarations.get(name);
        return held != null && held.stated ? held.sort : null;
    }

    private void put(String name, Sort sort, boolean stated) {
        Declared held = declarations.get(name);
        if (stated && (held == null || !held.stated)) {
            forget();
        }
        if (held != null && held.sort != sort) {
            String detail = held.sort + " and " + sort;
            top().sortConflicts.put(name, detail);
            refuse(SORT_CONFLICT + ":" + name, "this corpus states one "
                    + "solver name at two sorts, " + detail + ": the "
                    + "first stands and nothing is composed over it");
            declarations.put(name, new Declared(held.sort,
                    stated || held.stated, true));
            return;
        }
        declarations.put(name, new Declared(sort,
                stated || held != null && held.stated, true));
    }

    public Map<String, String> sortConflicts() {
        return Collections.unmodifiableMap(root.sortConflicts);
    }

    public Map<String, String> nameCollisions() {
        return symbols.collisions();
    }

    public boolean stated(String name) {
        Declared held = declarations.get(name);
        return held != null && held.stated;
    }

    public boolean declared(String name) {
        Declared held = declarations.get(name);
        return held != null && held.inQuery;
    }

    public String sharedBody(String name) {
        SharedTerm held = sharedTerms.get(name);
        return held == null ? null : held.body;
    }

    public boolean defined(String name) {
        return declared(name) || sharedTerms.containsKey(name);
    }

    public Sort declaredSort(String name) {
        Declared held = declarations.get(name);
        return held != null && held.inQuery ? held.sort : null;
    }

    public boolean minted(String name) {
        return defined(name) && !usedSymbols.contains(name);
    }

    private void sideCondition(String predicate) {
        if (predicate == null || predicate.isEmpty()
                || "true".equals(predicate)) {
            return;
        }
        top().condition(predicate);
    }

    private void refuse(String subject, String detail) {
        top().refusal(subject);
        if (detail != null && !detail.isEmpty()) {
            unsupportedDetail.put(subject, detail);
        }
    }

    private Term cut(String subject, String detail, Sort expected,
                     String javaType) {
        top().cuts.add(subject);
        refuse(CUT + ":" + subject, detail);
        return leaf(expected, javaType);
    }

    private Term unstated(String subject, String detail, Sort expected,
                          String javaType) {
        refuse(UNSTATED + ":" + subject, detail);
        return leaf(expected, javaType);
    }

    private static Sort leafSort(String javaType, Sort expected) {
        if (expected != null && expected.containerState()) return expected;
        Sort own = JavaSmtSorts.sortOfJava(javaType);
        return own != Sort.VALUE ? own : expected;
    }

    private Term leaf(Sort expected, String javaType) {
        return free(leafSort(javaType, expected),
                JavaPrimitiveSmtSemantics.widthOfJavaType(javaType));
    }

    private Term free(Sort sort, IntegralWidth width) {
        Sort declared = sort == null || sort == Sort.UNKNOWN
                ? Sort.VALUE : sort;
        String name = symbols.mint(HAVOC,
                scope + "#" + declared + "#" + freeConstants++, 10);
        declare(name, declared);
        return Term.of(name, declared, width == IntegralWidth.NONE
                ? IntegralWidth.JAVA_INT : width);
    }

    private int freeConstants;

    private static final class Stated {
        private final String formula;
        private final String label;
        private volatile List<String> names;
        private boolean reached;

        private Stated(String formula, String label) {
            this.formula = formula;
            this.label = label;
        }

        private List<String> names() {
            List<String> read = names;
            if (read == null) {
                read = SmtNames.names(formula);
                names = read;
            }
            return read;
        }

        private String render() {
            return label.isEmpty() ? "(assert " + formula + ")"
                    : "(assert (! " + formula + " :named " + label + "))";
        }
    }

    public void assertNamed(String name, String formula) {
        assertions.add(new Stated(formula, name));
    }

    public void retract(List<String> names) {
        if (names.isEmpty()) return;
        Set<String> taken = new LinkedHashSet<String>(names);
        assertions.removeIf(held -> taken.contains(held.label));
    }

    public void assertPlain(String formula) {
        if (formula == null || formula.isEmpty()
                || "true".equals(formula)) {
            return;
        }
        if (assertedOnce.add(formula)) {
            assertions.add(new Stated(formula, ""));
        }
    }

    public List<String> facts(Iterable<String> texts) {
        return facts(SmtNames.named(texts));
    }

    public List<String> facts(SmtNames.Named names) {
        Set<String> reached = new LinkedHashSet<String>(SmtNames.preambleNames());
        for (Declaration declaration : reachedBy(names)) {
            reached.add(declaration.name);
        }
        List<String> stated = new ArrayList<String>();
        Map<String, Boolean> closed = new HashMap<String, Boolean>();
        for (Stated held : assertions) {
            if (!held.label.isEmpty()) continue;
            boolean whole = true;
            for (String name : held.names()) {
                if (stands(name, reached, closed)) continue;
                whole = false;
                break;
            }
            if (whole && !stated.contains(held.formula)) {
                stated.add(held.formula);
            }
        }
        return stated;
    }

    private boolean stands(String name, Set<String> reached,
                           Map<String, Boolean> closed) {
        if (SmtNames.BUILTIN.contains(name) || reached.contains(name)) {
            return true;
        }
        SharedTerm shared = sharedTerms.get(name);
        if (shared == null) return false;
        Boolean known = closed.get(name);
        if (known != null) return known;
        closed.put(name, Boolean.FALSE);
        for (String inner : shared.names()) {
            if (!stands(inner, reached, closed)) return false;
        }
        closed.put(name, Boolean.TRUE);
        return true;
    }

    public Map<String, String> cuts() {
        Map<String, String> named = new LinkedHashMap<String, String>();
        for (String cut : root.cuts) {
            named.put(cut,
                    unsupportedDetail.getOrDefault(CUT + ":" + cut, ""));
        }
        return named;
    }

    public Map<String, String> pinnedReturns() {
        return Collections.unmodifiableMap(root.pinnedReturns);
    }

    public List<Unbound> unbound() {
        return Collections.unmodifiableList(root.unbound);
    }

    public static final class Unbound {
        public static final String FREE = "FREE";
        public static final String HELD = "HELD";
        public static final String CONSTANT = "CONSTANT";
        public static final String EXPORTED = "EXPORTED";
        public static final String BOUNDED = "BOUNDED";
        public static final String UNPAIRED = "UNPAIRED";
        public static final String PRODUCER_UNSTATED = "producer unstated";

        public final String kind;
        public final String subject;
        public final String value;
        public final String reason;
        public final List<String> movesWith;
        public final String arm;

        Unbound(String kind, String subject, String value, String reason,
                List<String> movesWith, String arm) {
            this.kind = kind;
            this.subject = subject;
            this.value = value;
            this.reason = reason;
            this.movesWith = Collections.unmodifiableList(movesWith);
            this.arm = arm;
        }
    }

    public void freedArrival(String symbol, String why) {
        freed(symbol, why, Collections.<String>emptySet());
    }

    public static final String UNCAPTURED = "its GROW re-run did not land: "
            + "the regions GROW grew ran uninstrumented in this session, "
            + "so the version this read saw, which no write row states, may "
            + "be one of their writes: free, never held";

    public void freedUncaptured(String subject) {
        freed(subject, UNCAPTURED, Collections.<String>emptySet());
    }

    public void held(String subject, String value, String why) {
        top().unbound(new Unbound(Unbound.HELD, subject, value,
                Unbound.PRODUCER_UNSTATED + ": " + why,
                Collections.<String>emptyList(), arm));
    }

    public void settledByRefusedProducer(String kind, String subject,
                                         String value, String rule) {
        top().unbound.add(new Unbound(kind, subject, value, rule,
                Collections.<String>emptyList(), arm));
    }

    public static boolean settled(String kind) {
        return Unbound.CONSTANT.equals(kind) || Unbound.EXPORTED.equals(kind)
                || Unbound.BOUNDED.equals(kind)
                || Unbound.UNPAIRED.equals(kind);
    }

    public void unpaired(String symbol, String reason) {
        root.unbound.add(new Unbound(Unbound.UNPAIRED, symbol, "", reason,
                Collections.<String>emptyList(), ""));
    }

    public static final class Declaration {
        public final String name;
        public final String sort;
        public final String body;

        private Declaration(String name, String sort, String body) {
            this.name = name;
            this.sort = sort;
            this.body = body;
        }

        public String render() {
            return body.isEmpty()
                    ? "(declare-const " + name + " " + sort + ")"
                    : "(define-fun " + name + " () " + sort + " " + body
                    + ")";
        }
    }

    public List<Declaration> reachedBy(Iterable<String> texts) {
        return reachedBy(SmtNames.named(texts));
    }

    public List<Declaration> reachedBy(SmtNames.Named texts) {
        List<Declaration> ordered = new ArrayList<Declaration>();
        Set<String> done = new HashSet<String>();
        List<Iterator<String>> names = new ArrayList<Iterator<String>>();
        List<SharedTerm> bodies = new ArrayList<SharedTerm>();
        names.add(held(texts).iterator());
        bodies.add(null);
        while (!names.isEmpty()) {
            int top = names.size() - 1;
            if (!names.get(top).hasNext()) {
                names.remove(top);
                SharedTerm shared = bodies.remove(top);
                if (shared != null) {
                    ordered.add(new Declaration(shared.name,
                            shared.sort.smt, shared.body));
                }
                continue;
            }
            String token = names.get(top).next();
            if (!done.add(token)) continue;
            SharedTerm shared = sharedTerms.get(token);
            if (shared != null) {
                names.add(shared.names().iterator());
                bodies.add(shared);
                continue;
            }
            Declared held = declarations.get(token);
            if (held != null && held.inQuery) {
                ordered.add(new Declaration(token, held.sort.smt, ""));
            }
        }
        return ordered;
    }

    private List<String> held(SmtNames.Named texts) {
        List<String> held = new ArrayList<String>();
        if (sharedTerms.size() + declarations.size() >= texts.size()) {
            for (String name : texts) {
                if (sharedTerms.containsKey(name)
                        || declarations.containsKey(name)) {
                    held.add(name);
                }
            }
            return held;
        }
        Set<String> own = new HashSet<String>(sharedTerms.keySet());
        own.addAll(declarations.keySet());
        for (String name : own) {
            if (texts.position(name) >= 0) held.add(name);
        }
        held.sort(Comparator.comparingInt(texts::position));
        return held;
    }

    public Set<String> reachedSymbols(Iterable<String> texts) {
        Set<String> into = new LinkedHashSet<String>();
        Set<String> seen = new LinkedHashSet<String>();
        for (String text : texts) reachedSymbols(text, seen, into);
        return into;
    }

    private void reachedSymbols(String text, Set<String> seen,
                                Set<String> into) {
        if (text == null || text.isEmpty()) return;
        Deque<Iterator<String>> names = new ArrayDeque<Iterator<String>>();
        names.push(SmtNames.names(text).iterator());
        while (!names.isEmpty()) {
            if (!names.peek().hasNext()) {
                names.pop();
                continue;
            }
            String name = names.peek().next();
            if (SmtNames.BUILTIN.contains(name) || !seen.add(name)) continue;
            SharedTerm shared = sharedTerms.get(name);
            if (shared != null) {
                names.push(shared.names().iterator());
                continue;
            }
            if (minted(name)) continue;
            into.add(name);
        }
    }

    public List<String> preambleLines() {
        List<String> lines = new ArrayList<String>();
        lines.add("(set-logic ALL)");
        lines.add("(set-option :produce-models true)");
        for (String line : VmTermLowering.preamble()) lines.add(line);
        lines.add(VmTermLowering.JAVA_INT_TO_STRING);
        lines.add(VmTermLowering.JAVA_ASCII_LOWER);
        lines.add(VmTermLowering.JAVA_ASCII_UPPER);
        lines.add(JavaPrimitiveSmtSemantics.INT_WRAP_DEFINITION);
        lines.add(JavaPrimitiveSmtSemantics.LONG_WRAP_DEFINITION);
        return lines;
    }

    private void appendPreamble(StringBuilder query,
                                Iterable<String> texts) {
        query.append("; GraphChecker composed query").append('\n');
        for (String line : SmtNames.reachedPreamble(preambleLines(), texts)) {
            query.append(line).append('\n');
        }
    }

    public String body(Iterable<String> alsoAsked) {
        List<String> texts = new ArrayList<String>();
        for (Stated held : assertions) texts.add(held.formula);
        if (alsoAsked != null) {
            for (String text : alsoAsked) {
                if (text != null && !text.isEmpty()) texts.add(text);
            }
        }
        List<Declaration> declared = reachedBy(texts);
        List<String> reaching = new ArrayList<String>(texts);
        for (Declaration declaration : declared) {
            reaching.add(declaration.render());
        }
        StringBuilder query = new StringBuilder();
        appendPreamble(query, reaching);
        for (Declaration declaration : declared) {
            query.append(declaration.render()).append('\n');
        }
        for (Stated held : assertions) {
            query.append(held.render()).append('\n');
        }
        return SmtNames.legalSymbols(query.toString());
    }


    public static String locationKey(LocationId location) {
        return location == null ? "" : location.key();
    }

    public static String locationKey(JsonObject location) {
        if (location == null || location.size() == 0) return "";
        String kind = primitiveString(location, "locationKind");
        if (kind.isEmpty()) return "";
        String owner = primitiveString(location, "ownerSymRid");
        if (owner.isEmpty()) {
            long rid = optionalLongInteger(location, "ownerSymRid", 0L);
            owner = rid == 0L ? "" : Long.toString(rid);
        }
        if (owner.isEmpty()) return "";
        String slot = primitiveString(location, "slot");
        if (slot.isEmpty()) {
            slot = Long.toString(optionalLongInteger(location, "slot", 0L));
        }
        return LocationId.of(locationKind(kind), owner, slot).key();
    }

    private static LocationKind locationKind(String kind) {
        String value = kind.toUpperCase();
        if (value.startsWith("STATIC")) return LocationKind.STATIC;
        if (value.startsWith("ARRAY")) return LocationKind.ARRAY;
        if (value.startsWith("MAP")) return LocationKind.MAP;
        return LocationKind.INSTANCE;
    }

    private static JsonElement observedVersionExpression(JsonObject node) {
        if (!VmRows.joinable(node)) return null;
        JsonElement observed = node.get(VmRows.OBSERVED_VERSION);
        if (observed == null || !observed.isJsonObject()) return null;
        return observed.getAsJsonObject().get("expression");
    }

    private static final String SEPARATOR = "|";


    public Term dispatch(JsonElement expression, Sort expected,
                        String origin) {
        return memoized(expression, expected, () -> {
            Term value = compact(lowered(expression, expected, origin));
            if (expression != null && expression.isJsonObject()) {
                JsonElement observed = expression.getAsJsonObject()
                        .get(VmRows.RECORDED_READING);
                if (observed != null && !observed.isJsonNull()) {
                    recordedReading(value, observed, origin);
                }
            }
            return value;
        }, () -> {
            cycle(origin);
            return free(expected, IntegralWidth.NONE);
        });
    }

    private Term compact(Term value) {
        String text = value.sort == Sort.BOOL ? value.text
                : named("term_dag__", value.sort, value.text);
        String nullness = named("defined_dag__", Sort.BOOL,
                value.stringNullness);
        String defined = named("defined_dag__", Sort.BOOL,
                value.precondition);
        if (text.equals(value.text) && nullness.equals(value.stringNullness)
                && defined.equals(value.precondition)) {
            return value;
        }
        return value.withText(text, nullness).withPrecondition(defined);
    }

    static final int NAMED_TEXT_CHARS = 2048;

    private String named(String prefix, Sort sort, String text) {
        if (text == null || text.length() <= NAMED_TEXT_CHARS
                || text.charAt(0) != '(' || sort == Sort.UNKNOWN) {
            return text;
        }
        return shared(prefix, sort, text);
    }

    private Term lowered(JsonElement expression, Sort expected,
                         String origin) {
        if (expression == null || expression.isJsonNull()
                || !expression.isJsonObject()) {
            return refuse(Reason.ABSENT_EXPRESSION, origin, "",
                    expected == null ? Sort.REF : expected);
        }
        JsonObject object = expression.getAsJsonObject();
        String type = optionalString(object, "_type");
        if ("SymbolExpression".equals(type)) {
            return symbolTerm(object, expected);
        }
        if (ContainerSmtCodec.constantKind(type)) {
            return constant(object, expected, origin);
        }
        if ("BinaryExpression".equals(type)) {
            return binary(object, origin);
        }
        if ("OpStrExpression".equals(type)) {
            return stringOperation(object, origin);
        }
        if ("TypeCastExpression".equals(type)) {
            return typeCast(object, origin);
        }
        if (VmRows.GUARDED_READ_TYPE.equals(type)) {
            return guardedReadTerm(object, expected, origin);
        }
        if (VmExpressionIr.consumerBoundary(object)) {
            return dispatch(object.get(VmExpressionIr.EXPRESSION), expected,
                    origin + ":consumer-boundary");
        }
        if ("MethodExpression".equals(type)) {
            return methodTerm(object, origin);
        }
        if (ContainerSmtCodec.handles(object)) {
            return containerTerm(object, false, origin);
        }
        if (ContainerSmtCodec.handlesField(object)) {
            return containerTerm(object, true, origin);
        }
        return refuse(Reason.UNKNOWN_EXPRESSION_TYPE, origin,
                type.isEmpty() ? "MISSING_TYPE" : type, expected);
    }

    private Term methodTerm(JsonObject expression, String origin) {
        String method = optionalString(expression, "_name");
        Term related = knownCall(method, array(expression, "_param_list"),
                origin);
        if (related != null) return related;
        if (VmExpressionIr.isJavaSplitElement(method)) {
            JsonElement element = StringIdentities.splitElement(expression);
            return element != null
                    ? dispatch(element, null, origin + ":split-element")
                    : splitElement(array(expression, "_param_list"), origin);
        }
        Term result = dispatch(expression.get("_res_exp"), null, origin);
        return refuse(Reason.MODEL_SEMANTICS_MISSING, origin,
                "MethodExpression:" + firstNonBlank(method, "unknown"),
                result.sort);
    }


    private static Term onTimeline(Term constant, Term other,
                                   Map<String, Long> bases) {
        if (constant.sort != Sort.INT || other.sort != Sort.INT) {
            return constant;
        }
        String literal = constant.text.trim();
        BigInteger value;
        try {
            value = literal.startsWith("(-")
                    ? new BigInteger(literal.substring(2,
                    literal.length() - 1).trim()).negate()
                    : new BigInteger(literal);
        } catch (NumberFormatException | StringIndexOutOfBoundsException
                notAConstant) {
            return constant;
        }
        Long base = bases.get(instantOf(SExpression.parse(other.text, 0)));
        if (base == null) return constant;
        return Term.vm(JavaPrimitiveSmtSemantics.integralLiteral(
                value.subtract(BigInteger.valueOf(base)).toString()),
                constant.sort, constant.integralWidth);
    }

    private static String instantOf(SExpression term) {
        if (term == null) return "";
        if (term.atom()) return term.text();
        List<SExpression> parts = term.children();
        String head = term.head();
        if (parts.size() == 2 && ("java_long_wrap".equals(head)
                || "java_int_wrap".equals(head))) {
            return instantOf(parts.get(1));
        }
        if (parts.size() == 3 && ("+".equals(head) || "-".equals(head))) {
            boolean spanAfter = constantAtom(parts.get(2));
            if (spanAfter) return instantOf(parts.get(1));
            if ("+".equals(head) && constantAtom(parts.get(1))) {
                return instantOf(parts.get(2));
            }
        }
        return "";
    }

    private static boolean constantAtom(SExpression term) {
        return term.atom() && !term.text().isEmpty()
                && Character.isDigit(term.text().charAt(0));
    }

    private Term binary(JsonObject expression, String origin) {
        String operator = JavaPrimitiveSmtSemantics.canonicalVmOperator(
                optionalString(expression, "_op"));
        JsonElement leftExpression = expression.get("_left");
        if (leftExpression == null || leftExpression.isJsonNull()) {
            return unary(expression, operator, origin);
        }
        JsonElement rightExpression = expression.get("_right");
        Term left;
        Term right;
        if (named(leftExpression) && !named(rightExpression)) {
            right = dispatch(rightExpression, null, origin + ":right");
            left = dispatch(leftExpression, right.sort, origin + ":left");
        } else {
            left = dispatch(leftExpression, null, origin + ":left");
            right = dispatch(rightExpression, left.sort, origin + ":right");
        }
        if (left.sort != right.sort && right.isZero()
                && left.sort == Sort.REF) {
            right = result("nullRef", Sort.REF);
        } else if (left.sort != right.sort && left.isZero()
                && right.sort == Sort.REF) {
            left = result("nullRef", Sort.REF);
        }
        if ("--".equals(operator) || "==".equals(operator)
                || "!=".equals(operator)
                || !VmExpressionIr.comparison(operator).isEmpty()) {
            Map<String, Long> bases = clockBases.get(scope);
            if (bases != null) {
                Term instant = onTimeline(left, right, bases);
                right = onTimeline(right, left, bases);
                left = instant;
            }
        }
        if ("--".equals(operator)) {
            if (left.sort == Sort.INT
                    && left.integralWidth == IntegralWidth.NONE) {
                left = result(left.text, Sort.INT, IntegralWidth.JAVA_LONG,
                        left);
            }
            if (right.sort == Sort.INT
                    && right.integralWidth == IntegralWidth.NONE) {
                right = result(right.text, Sort.INT, IntegralWidth.JAVA_LONG,
                        right);
            }
            if (left.sort == Sort.INT && right.sort == Sort.INT
                    && left.integralWidth == IntegralWidth.JAVA_LONG
                    && right.integralWidth == IntegralWidth.JAVA_LONG) {
                return result(JavaPrimitiveSmtSemantics
                        .integralCompareResult(left.text, right.text),
                        Sort.INT, IntegralWidth.JAVA_INT, left, right);
            }
            return refuse(Reason.MALFORMED_JVM_LCMP_OPERANDS,
                    origin, left.sort + ":" + left.integralWidth + ":"
                            + right.sort + ":" + right.integralWidth,
                    Sort.INT);
        }
        if ("--l".equals(operator) || "--g".equals(operator)) {
            if (left.sort == right.sort && left.sort.floating()) {
                return result(JavaPrimitiveSmtSemantics
                        .floatingCompareResult(left.text, right.text,
                                "--g".equals(operator)), Sort.INT,
                        IntegralWidth.JAVA_INT, left, right);
            }
            return refuse(Reason.MALFORMED_JVM_FLOATING_COMPARE_OPERANDS,
                    origin, operator + ":" + left.sort + ":" + right.sort,
                    Sort.INT);
        }
        if (left.sort != right.sort && numeric(left.sort)
                && numeric(right.sort)
                && (left.sort.floating() || right.sort.floating())) {
            Sort promoted = left.sort == Sort.FLOAT64
                    || right.sort == Sort.FLOAT64
                    ? Sort.FLOAT64 : Sort.FLOAT32;
            left = floatingPromotion(left, promoted,
                    origin + ":left");
            right = floatingPromotion(right, promoted,
                    origin + ":right");
        }
        boolean equality = "==".equals(operator) || "!=".equals(operator);
        if (equality && (left.sort == Sort.STRING && right.isNullReference()
                || right.sort == Sort.STRING && left.isNullReference())) {
            Term string = left.sort == Sort.STRING ? left : right;
            if (string.stringNullness.isEmpty()) {
                return refuse(Reason.JAVA_STRING_NULLNESS_UNKNOWN, origin,
                        operator, Sort.BOOL);
            }
            return result("!=".equals(operator)
                    ? "(not " + string.stringNullness + ")"
                    : string.stringNullness, Sort.BOOL, left, right);
        }
        if (equality && (left.sort == Sort.REF && right.sort == Sort.STRING
                || left.sort == Sort.STRING && right.sort == Sort.REF)
                && !left.isNullReference() && !right.isNullReference()) {
            Term string = left.sort == Sort.STRING ? left : right;
            if (!"false".equals(string.stringNullness)) {
                return refuse(Reason.BINARY_SORT_CONFLICT, origin,
                        operator + ":REF!=STRING (a String that may be null)",
                        Sort.BOOL);
            }
            sideCondition(ContainerStateModel.stringRefFacts(string.text));
            Term ref = Term.of(ContainerStateModel.stringRef(string.text),
                    Sort.REF);
            if (left == string) {
                left = ref;
            } else {
                right = ref;
            }
            return equality(expression, operator, left, right, origin);
        }
        if (left.sort != right.sort && equality
                && (left.isNullReference() || right.isNullReference())) {
            return result("!=".equals(operator) ? "true" : "false",
                    Sort.BOOL, left, right);
        }
        if ("&&".equals(operator) || "||".equals(operator)) {
            if (left.sort != Sort.BOOL || right.sort != Sort.BOOL) {
                return refuse(Reason.NON_BOOLEAN_LOGIC, origin,
                        operator + ":" + left.sort + ":" + right.sort,
                        Sort.BOOL);
            }
            boolean conjunction = "&&".equals(operator);
            return shortCircuit("(" + (conjunction ? "and" : "or") + " "
                    + left.text + " " + right.text + ")", left, right,
                    conjunction);
        }
        if (left.sort != right.sort
                && (left.sort == Sort.VALUE) != (right.sort == Sort.VALUE)
                && !equality) {
            if (left.sort == Sort.VALUE) {
                left = fromValue(left, expressionJavaType(
                        expression.get("_left")));
            } else {
                right = fromValue(right, expressionJavaType(
                        expression.get("_right")));
            }
        }
        if (left.sort != right.sort) {
            Sort resultSort = equality || !comparison(operator).isEmpty()
                    ? Sort.BOOL : left.sort;
            return refuse(Reason.BINARY_SORT_CONFLICT, origin,
                    operator + ":" + left.sort + "!=" + right.sort,
                    resultSort);
        }
        if (equality) {
            return equality(expression, operator, left, right, origin);
        }
        String smt = comparison(operator);
        if (!smt.isEmpty()) {
            if (!numeric(left.sort) || !numeric(right.sort)) {
                return refuse(Reason.NON_NUMERIC_COMPARISON, origin,
                        operator + ":" + left.sort, Sort.BOOL);
            }
            if (left.sort.floating()) {
                return result(JavaPrimitiveSmtSemantics.floatingComparison(
                        operator, left.text, right.text), Sort.BOOL,
                        left, right);
            }
            return result("(" + smt + " " + left.text + " " + right.text
                    + ")", Sort.BOOL, left, right);
        }
        if (bitwiseOperator(operator)) {
            IntegralWidth width = promotedIntegralWidth(left, right);
            if (width == IntegralWidth.NONE) {
                return refuse(
                        Reason.AMBIGUOUS_JAVA_INTEGRAL_BITWISE_WIDTH, origin,
                        operator + ":" + left.integralWidth + ":"
                                + right.integralWidth, Sort.INT);
            }
            return result(JavaPrimitiveSmtSemantics.bitwise(operator,
                    left.text, right.text, width), Sort.INT, width,
                    left, right);
        }
        if (shiftOperator(operator)) {
            if (left.sort != Sort.INT || right.sort != Sort.INT
                    || left.integralWidth == IntegralWidth.NONE) {
                return refuse(Reason.AMBIGUOUS_JAVA_INTEGRAL_SHIFT, origin,
                        operator + ":" + left.integralWidth + ":"
                                + right.integralWidth, Sort.INT);
            }
            return result(JavaPrimitiveSmtSemantics.shift(operator,
                    left.text, right.text, left.integralWidth), Sort.INT,
                    left.integralWidth, left, right);
        }
        if (arithmeticOperator(operator)) {
            return arithmeticTerm(operator, left, right, origin);
        }
        return refuse(Reason.BINARY_OPERATOR, origin, operator, Sort.BOOL);
    }

    private Term unary(JsonObject expression, String operator,
                       String origin) {
        Term operand = dispatch(expression.get("_right"), null,
                origin + ":operand");
        Sort operandSort = operand.sort;
        if ("-".equals(operator) && numeric(operandSort)) {
            if (operandSort.floating()) {
                return result(JavaPrimitiveSmtSemantics.floatingNegate(
                        operand.text), operandSort, operand);
            }
            if (operand.integralWidth != IntegralWidth.NONE) {
                return result(JavaPrimitiveSmtSemantics.wrap("(- "
                        + operand.text + ")", operand.integralWidth),
                        Sort.INT, operand.integralWidth, operand);
            }
            return refuse(Reason.AMBIGUOUS_JAVA_INTEGRAL_UNARY_WIDTH, origin,
                    firstNonBlank(operator, "MISSING"), Sort.INT);
        }
        if ("~".equals(operator) && operandSort == Sort.INT
                && operand.integralWidth != IntegralWidth.NONE) {
            return result(JavaPrimitiveSmtSemantics.complement(operand.text,
                    operand.integralWidth), Sort.INT, operand.integralWidth,
                    operand);
        }
        return refuse(Reason.NON_NUMERIC_OR_UNKNOWN_UNARY, origin,
                firstNonBlank(operator, "MISSING") + ":" + operandSort,
                operandSort);
    }

    private Term equality(JsonObject expression, String operator,
                          Term left, Term right, String origin) {
        if (left.text.equals(right.text)) {
            return result("==".equals(operator) ? "true" : "false",
                    Sort.BOOL, left, right);
        }
        if (left.sort == Sort.STRING) {
            return stringIdentity(expression, operator, left, right, origin);
        }
        if (left.sort.floating()) {
            return result(JavaPrimitiveSmtSemantics.floatingComparison(
                    operator, left.text, right.text), Sort.BOOL,
                    left, right);
        }
        String equals = "(= " + left.text + " " + right.text + ")";
        return result("!=".equals(operator) ? "(not " + equals + ")"
                : equals, Sort.BOOL, left, right);
    }

    private Term stringIdentity(JsonObject expression, String operator,
                                Term left, Term right, String origin) {
        if (!left.stringReferenceOrigin.isEmpty()
                && left.stringReferenceOrigin.equals(
                right.stringReferenceOrigin)) {
            return result("!=".equals(operator) ? "false" : "true",
                    Sort.BOOL, left, right);
        }
        Term literalSide = stringLiteral(expression.get("_left")) != null
                ? left
                : stringLiteral(expression.get("_right")) != null
                ? right : null;
        if (literalSide != null) {
            Term symbolSide = literalSide == left ? right : left;
            String equals = ContainerSmtCodec.materializedStringEquality(
                    left.text, right.text, symbolSide.stringNullness);
            if (!equals.isEmpty()) {
                return result("!=".equals(operator) ? "(not " + equals + ")"
                        : equals, Sort.BOOL, left, right);
            }
        }
        return dependent(refuse(Reason.MODEL_SEMANTICS_MISSING, origin,
                "JAVA_STRING_REFERENCE_IDENTITY:" + operator, Sort.BOOL),
                left, right);
    }

    private Term arithmeticTerm(String operator, Term left, Term right,
                                String origin) {
        if (!numeric(left.sort) || !numeric(right.sort)) {
            return refuse(Reason.NON_NUMERIC_ARITHMETIC, origin,
                    operator + ":" + left.sort, left.sort);
        }
        Sort resultSort = left.sort;
        if ("%".equals(operator) && resultSort.floating()) {
            return refuse(Reason.JAVA_FLOATING_REMAINDER_UNMODELED, origin,
                    "", resultSort);
        }
        if (resultSort.floating()) {
            String floating = JavaPrimitiveSmtSemantics.floatingArithmetic(
                    operator, left.text, right.text);
            if (floating != null) {
                return result(floating, resultSort, left, right);
            }
            return refuse(Reason.JAVA_FLOATING_OPERATOR_UNMODELED, origin,
                    operator, resultSort);
        }
        IntegralWidth width = promotedIntegralWidth(left, right);
        if (width == IntegralWidth.NONE) {
            return refuse(Reason.AMBIGUOUS_JAVA_INTEGRAL_BINARY_WIDTH,
                    origin, operator + ":" + left.integralWidth + ":"
                            + right.integralWidth, Sort.INT);
        }
        if ("@".equals(operator) || "/".equals(operator)
                || "%".equals(operator)) {
            String quotient = "%".equals(operator)
                    ? JavaPrimitiveSmtSemantics.integralRemainder(left.text,
                    right.text, width)
                    : JavaPrimitiveSmtSemantics.integralDivision(left.text,
                    right.text, width);
            return definedResult(quotient, Sort.INT, width,
                    JavaPrimitiveSmtSemantics.integralDivisorDefined(
                            right.text), left, right);
        }
        return result(JavaPrimitiveSmtSemantics.wrap("("
                + arithmetic(operator) + " " + left.text + " " + right.text
                + ")", width), Sort.INT, width, left, right);
    }


    private Term constant(JsonObject expression, Sort expected,
                          String origin) {
        String raw = optionalString(expression, "_exp");
        String javaType = optionalString(expression, "_java_type");
        String value = constantPayload(raw);
        Sort sort = JavaSmtSorts.sortOfJava(javaType);
        if (expected == Sort.BOOL && (sort == Sort.BOOL
                || sort == Sort.INT)) {
            return booleanLiteral(value, raw, origin);
        }
        if (expected == Sort.REF && ("0".equals(value)
                || VmExpressionIr.SYMBOLIC_NULL.equals(raw))) {
            return result("nullRef", Sort.REF);
        }
        if (sort == Sort.BOOL) return booleanLiteral(value, raw, origin);
        if (sort.floating()) {
            String literal = JavaPrimitiveSmtSemantics.floatingLiteral(value,
                    floatingKind(sort));
            return literal == null
                    ? refuse(Reason.INVALID_NUMERIC_LITERAL, origin,
                    sort + ":" + firstNonBlank(raw, "MISSING"), sort)
                    : result(literal, sort);
        }
        if (sort == Sort.INT) {
            String literal = JavaPrimitiveSmtSemantics
                    .integralLiteral(value);
            return literal.isEmpty()
                    ? refuse(Reason.INVALID_NUMERIC_LITERAL, origin,
                    sort + ":" + firstNonBlank(raw, "MISSING"), sort)
                    : result(literal, Sort.INT, JavaPrimitiveSmtSemantics
                    .widthOfJavaType(javaType));
        }
        if (sort == Sort.STRING) {
            return Term.nonNullString(quote(value), "true");
        }
        if (VmExpressionIr.SYMBOLIC_NULL.equals(raw)) {
            return result("nullRef", Sort.REF);
        }
        return refuse(Reason.UNSUPPORTED_CONSTANT_TYPE, origin,
                firstNonBlank(javaType, "MISSING"),
                sort == Sort.VALUE ? Sort.REF : sort);
    }

    private Term booleanLiteral(String value, String raw, String origin) {
        if (!"0".equals(value) && !"1".equals(value)) {
            return refuse(Reason.INVALID_JAVA_BOOLEAN_LITERAL, origin,
                    firstNonBlank(raw, "MISSING"), Sort.BOOL);
        }
        return result("1".equals(value) ? "true" : "false", Sort.BOOL);
    }


    private Term stringOperation(JsonObject expression, String origin) {
        JsonObject rendered = StringIdentities.asRenderings(expression);
        if (rendered != null) return dispatch(rendered, null, origin);
        String operation = optionalString(expression, "_name");
        boolean negated = optionalBool(expression, "_is_not", false);
        JsonArray params = array(expression, "_param_list");
        if ("equalsIgnoreCase".equals(operation)) {
            StringIdentities.BooleanTest test =
                    StringIdentities.booleanTest(params, true);
            if (test != null) {
                Term flag = dispatch(test.flag, null,
                        origin + ":equalsIgnoreCase");
                return flag.sort == Sort.BOOL
                        ? booleanStringResult(truth(test, flag), negated,
                        flag.precondition)
                        : codecGap(operation, "NON_BOOLEAN_RENDERING", origin,
                        Sort.BOOL);
            }
            return equalsIgnoreCase(params, negated, origin);
        }
        if ("isEmpty".equals(operation)) {
            StringParameters strings = stringParameters(params, 1,
                    operation, origin, Sort.BOOL);
            if (strings.terms == null) return strings.refusal;
            return booleanStringResult("(= (str.len "
                            + strings.terms.get(0).text + ") 0)", negated,
                    strings.defined);
        }
        if ("length".equals(operation)) {
            if (negated) {
                return codecGap(operation, "NEGATED_VALUE_OPERATION", origin,
                        Sort.INT);
            }
            StringParameters strings = stringParameters(params, 1,
                    operation, origin, Sort.INT);
            if (strings.terms == null) return strings.refusal;
            String text = "(str.len " + strings.terms.get(0).text + ")";
            Term length = definedResult(text, Sort.INT,
                    IntegralWidth.JAVA_INT, strings.defined);
            assertJavaIntegralDomain(text, "I");
            return length;
        }
        if ("charAt".equals(operation) || "indexOf".equals(operation)
                || "lastIndexOf".equals(operation)
                || "compareTo".equals(operation)) {
            if (negated) {
                return codecGap(operation, "NEGATED_VALUE_OPERATION", origin,
                        Sort.INT);
            }
            return "compareTo".equals(operation) ? compareTo(params, origin)
                    : stringPosition(operation, params, origin);
        }
        if ("equals".equals(operation)) {
            return stringEquals(params, negated, origin);
        }
        if ("startsWith".equals(operation) && params.size() == 3) {
            return startsWithAt(params, negated, origin);
        }
        if ("regionMatches".equals(operation)) {
            return regionMatches(params, negated, origin);
        }
        if ("contains".equals(operation) || "startsWith".equals(operation)
                || "endsWith".equals(operation)) {
            StringParameters strings = stringParameters(params, 2,
                    operation, origin, Sort.BOOL);
            if (strings.terms == null) return strings.refusal;
            String receiver = strings.terms.get(0).text;
            String argument = strings.terms.get(1).text;
            String predicate = "contains".equals(operation)
                    ? "(str.contains " + receiver + " " + argument + ")"
                    : "startsWith".equals(operation)
                    ? "(str.prefixof " + argument + " " + receiver + ")"
                    : "(str.suffixof " + argument + " " + receiver + ")";
            return booleanStringResult(predicate, negated, strings.defined);
        }
        if (negated) {
            return codecGap(firstNonBlank(operation, "unknown"),
                    "NEGATED_VALUE_OPERATION", origin, Sort.STRING);
        }
        if ("concat".equals(operation)) {
            if (params.size() == 0) {
                return codecGap(operation, "EMPTY", origin, Sort.STRING);
            }
            StringParameters strings = stringParameters(params,
                    params.size(), operation, origin, Sort.STRING);
            if (strings.terms == null) return strings.refusal;
            if (strings.terms.size() == 1) {
                return Term.nonNullString(strings.terms.get(0).text,
                        strings.defined);
            }
            StringBuilder result = new StringBuilder("(str.++");
            for (Term value : strings.terms) {
                result.append(' ').append(value.text);
            }
            return Term.nonNullString(result.append(')').toString(),
                    strings.defined);
        }
        if ("substring".equals(operation)
                || "subSequence".equals(operation)) {
            return substring(params, origin);
        }
        if ("toUpperCase".equals(operation)
                || "toLowerCase".equals(operation)) {
            boolean upper = "toUpperCase".equals(operation);
            Term converted = convertedConstant(params, upper, origin);
            return converted != null ? converted
                    : asciiCase(params, upper, origin);
        }
        if ("trim".equals(operation)) {
            return trim(params, origin);
        }
        if ("toString".equals(operation)) {
            return javaToString(params, origin);
        }
        if ("valueOf".equals(operation)) {
            return javaValueOf(params, origin);
        }
        Matcher radix = RADIX_STRING.matcher(firstNonBlank(operation, ""));
        if (radix.matches()) {
            return unsignedString(params, operation,
                    "Integer".equals(radix.group(1)) ? 32 : 64,
                    "Hex".equals(radix.group(2)) ? 4
                            : "Octal".equals(radix.group(2)) ? 3 : 1, origin);
        }
        return codecGap(firstNonBlank(operation, "unknown"),
                "UNSUPPORTED_OPERATION", origin, Sort.STRING);
    }

    private static final Pattern RADIX_STRING = Pattern.compile(
            "unsupportedPrimitiveStringConversion:java/lang/(Integer|Long)"
                    + "\\.to(Hex|Octal|Binary)String\\([IJ]\\)"
                    + "Ljava/lang/String;");

    private Term unsignedString(JsonArray params, String operation, int bits,
                                int shift, String origin) {
        if (params.size() != 1) {
            return codecGap(operation, "ARITY", origin, Sort.STRING);
        }
        Term value = dispatch(params.get(0), null, origin + ":unsigned");
        if (value.sort != Sort.INT) {
            return codecGap(operation, "NON_INTEGRAL_TERM", origin,
                    Sort.STRING);
        }
        BigInteger radix = BigInteger.ONE.shiftLeft(shift);
        String unsigned = "(mod " + value.text + " "
                + BigInteger.ONE.shiftLeft(bits) + ")";
        StringBuilder text = new StringBuilder("(str.++");
        for (int at = (bits + shift - 1) / shift - 1; at >= 0; at--) {
            BigInteger place = radix.pow(at);
            String digit = "(str.at \"0123456789abcdef\" (mod (div "
                    + unsigned + " " + place + ") " + radix + "))";
            text.append(' ').append(at == 0 ? digit : "(ite (>= " + unsigned
                    + " " + place + ") " + digit + " \"\")");
        }
        return Term.nonNullString(text.append(')').toString(),
                value.precondition);
    }

    private Term javaValueOf(JsonArray params, String origin) {
        if (params.size() != 1) {
            return codecGap("valueOf", "ARITY", origin, Sort.STRING);
        }
        Term value = dispatch(params.get(0), null, origin + ":valueOf");
        if (value.sort != Sort.STRING) return javaToString(params, origin);
        if (nullnessUnknown(Collections.singletonList(value))) {
            return refuse(Reason.JAVA_STRING_NULLNESS_UNKNOWN, origin,
                    "valueOf", Sort.STRING);
        }
        return Term.nonNullString("false".equals(value.stringNullness)
                ? value.text : "(ite " + value.stringNullness + " \"null\" "
                + value.text + ")", value.precondition);
    }

    private Term javaToString(JsonArray params, String origin) {
        if (params.size() != 1) {
            return codecGap("toString", "ARITY", origin, Sort.STRING);
        }
        String javaType = expressionJavaType(params.get(0));
        Term value = dispatch(params.get(0), null, origin + ":toString");
        if (value.sort == Sort.STRING) {
            if (nullnessUnknown(Collections.singletonList(value))) {
                return refuse(Reason.JAVA_STRING_NULLNESS_UNKNOWN, origin,
                        "toString", Sort.STRING);
            }
            return Term.nonNullString(value.text, stringDefinedness(
                    Collections.singletonList(value),
                    Collections.<Term>emptyList()));
        }
        if (value.sort == Sort.BOOL) {
            return Term.nonNullString("(ite " + value.text
                    + " \"true\" \"false\")", value.precondition);
        }
        boolean promoted = "BinaryExpression".equals(
                VmExpressionIr.typeOf(params.get(0)))
                && value.integralWidth != IntegralWidth.NONE;
        if (value.sort != Sort.INT
                || !DECIMAL_OR_CHAR.contains(javaType) && !promoted) {
            return codecGap("toString", "NON_INTEGRAL_TERM", origin,
                    Sort.STRING);
        }
        JavaPrimitiveSmtSemantics.IntegralDomain domain =
                JavaPrimitiveSmtSemantics.domainOfJavaType(javaType);
        String defined = domain == null ? value.precondition
                : and(Arrays.asList(value.precondition,
                VmTermLowering.integralRange(domain.lower, value.text,
                        domain.upper)));
        if ("C".equals(javaType)) {
            return Term.nonNullString("(str.from_code " + value.text + ")",
                    defined);
        }
        return Term.nonNullString("(java_int_to_string " + value.text + ")",
                defined);
    }

    private static final Set<String> DECIMAL_OR_CHAR = new LinkedHashSet<String>(
            Arrays.asList("B", "S", "I", "J", "C"));

    private Term trim(JsonArray params, String origin) {
        StringParameters strings = stringParameters(params, 1, "trim",
                origin, Sort.STRING);
        if (strings.terms == null) return strings.refusal;
        String text = strings.terms.get(0).text;
        String length = "(str.len " + text + ")";
        String begin = symbols.mint("trim_begin__", scope + "#" + trims, 10);
        String end = symbols.mint("trim_end__", scope + "#" + trims++, 10);
        declare(begin, Sort.INT);
        declare(end, Sort.INT);
        String blanks = "(re.* (re.range \"\\u{0}\" \" \"))";
        sideCondition(and(Arrays.asList("(<= 0 " + begin + ")",
                "(<= " + begin + " " + end + ")",
                "(<= " + end + " " + length + ")",
                "(str.in_re (str.substr " + text + " 0 " + begin + ") "
                        + blanks + ")",
                "(str.in_re (str.substr " + text + " " + end + " (- "
                        + length + " " + end + ")) " + blanks + ")",
                "(or (= " + begin + " " + end + ") (and (< 32 (str.to_code "
                        + "(str.at " + text + " " + begin + "))) (< 32 "
                        + "(str.to_code (str.at " + text + " (- " + end
                        + " 1))))))")));
        return Term.nonNullString("(str.substr " + text + " " + begin
                + " (- " + end + " " + begin + "))", strings.defined);
    }

    private int trims;

    private Term asciiCase(JsonArray params, boolean upper, String origin) {
        String operation = upper ? "toUpperCase" : "toLowerCase";
        StringParameters strings = stringParameters(params, 1, operation,
                origin, Sort.STRING);
        if (strings.terms == null) return strings.refusal;
        String text = strings.terms.get(0).text;
        return Term.nonNullString("(" + (upper ? "java_ascii_upper"
                        : "java_ascii_lower") + " " + text + ")",
                and(Arrays.asList(strings.defined, "(str.in_re " + text
                        + " (re.* (re.range \"\\u{0}\" \"\\u{7f}\")))")));
    }

    private Term equalsIgnoreCase(JsonArray params, boolean negated,
                                  String origin) {
        String operation = "equalsIgnoreCase";
        if (params.size() != 2) {
            return codecGap(operation, "ARITY", origin, Sort.BOOL);
        }
        Term receiver = dispatch(params.get(0), null,
                origin + ":" + operation + ":parameter0");
        Term argument = dispatch(params.get(1), null,
                origin + ":" + operation + ":parameter1");
        if (receiver.sort != Sort.STRING) {
            return codecGap(operation, "NON_STRING_PARAMETER", origin,
                    Sort.BOOL);
        }
        if (nullnessUnknown(Collections.singletonList(receiver))) {
            return refuse(Reason.JAVA_STRING_NULLNESS_UNKNOWN, origin,
                    operation + ":0", Sort.BOOL);
        }
        String defined = stringDefinedness(Collections.singletonList(
                receiver), Collections.singletonList(argument));
        if (argument.isNullReference()) {
            return booleanStringResult("false", negated, defined);
        }
        if (argument.sort != Sort.STRING) {
            return codecGap(operation, "ARGUMENT_DYNAMIC_TYPE_UNMODELED",
                    origin, Sort.BOOL);
        }
        if (argument.stringNullness.isEmpty()) {
            return refuse(Reason.JAVA_STRING_NULLNESS_UNKNOWN, origin,
                    operation + ":1", Sort.BOOL);
        }
        String literal = StringIdentities.stringLiteral(params.get(1));
        String other = receiver.text;
        if (literal == null) {
            literal = StringIdentities.stringLiteral(params.get(0));
            other = argument.text;
        }
        if (literal == null) {
            return codecGap(operation, "NO_LITERAL_SIDE", origin, Sort.BOOL);
        }
        List<String> chars = new ArrayList<String>();
        for (char one : literal.toCharArray()) chars.add(ignoringCase(one));
        String pattern = chars.isEmpty() ? "(str.to_re \"\")"
                : chars.size() == 1 ? chars.get(0)
                : "(re.++ " + String.join(" ", chars) + ")";
        return booleanStringResult(and(Arrays.asList(stringNonNull(argument),
                "(str.in_re " + other + " " + pattern + ")")), negated,
                defined);
    }

    private static String ignoringCase(char one) {
        return IGNORING_CASE.computeIfAbsent(one, key -> {
            char upper = Character.toUpperCase(one);
            char lower = Character.toLowerCase(upper);
            List<String> taken = new ArrayList<String>();
            for (int code = 0; code <= Character.MAX_VALUE; code++) {
                char other = Character.toUpperCase((char) code);
                if (code == one || other == upper
                        || Character.toLowerCase(other) == lower) {
                    taken.add("(str.to_re \"\\u{"
                            + Integer.toHexString(code) + "}\")");
                }
            }
            return taken.size() == 1 ? taken.get(0)
                    : "(re.union " + String.join(" ", taken) + ")";
        });
    }

    private static final Map<Character, String> IGNORING_CASE =
            new ConcurrentHashMap<Character, String>();

    private Term substring(JsonArray params, String origin) {
        if (params.size() != 2 && params.size() != 3) {
            return codecGap("substring", "ARITY", origin, Sort.STRING);
        }
        Term receiver = dispatch(params.get(0), null,
                origin + ":substring:receiver");
        if (receiver.sort != Sort.STRING) {
            return codecGap("substring", "NON_STRING_PARAMETER", origin,
                    Sort.STRING);
        }
        List<Term> bounds = new ArrayList<Term>();
        for (int index = 1; index < params.size(); index++) {
            Term bound = dispatch(params.get(index), Sort.INT,
                    origin + ":substring:bound" + index);
            if (bound.sort != Sort.INT) {
                return codecGap("substring", "NON_INT_PARAMETER", origin,
                        Sort.STRING);
            }
            bounds.add(bound);
        }
        if (nullnessUnknown(Collections.singletonList(receiver))) {
            return refuse(Reason.JAVA_STRING_NULLNESS_UNKNOWN, origin,
                    "substring", Sort.STRING);
        }
        String length = "(str.len " + receiver.text + ")";
        String begin = bounds.get(0).text;
        String end = bounds.size() == 2 ? bounds.get(1).text : length;
        String defined = and(Arrays.asList(stringDefinedness(
                        Collections.singletonList(receiver), bounds),
                "(<= 0 " + begin + ")", "(<= " + begin + " " + end + ")",
                "(<= " + end + " " + length + ")"));
        return Term.nonNullString("(str.substr " + receiver.text + " " + begin
                + " (- " + end + " " + begin + "))", defined);
    }

    static final int SPLIT_MAX = 8;

    private Term splitElement(JsonArray params, String origin) {
        if (params.size() != 3) {
            return codecGap("splitElement", "ARITY", origin, Sort.STRING);
        }
        String regex = StringIdentities.stringLiteral(params.get(1));
        Character delimiter = regex == null ? null
                : StringIdentities.literalDelimiter(regex);
        Integer index = StringIdentities.intLiteral(params.get(2));
        if (delimiter == null || index == null || index < 0
                || index > SPLIT_MAX) {
            return refuse(Reason.MODEL_SEMANTICS_MISSING, origin,
                    "java/lang/String.splitElement", Sort.STRING);
        }
        Term receiver = dispatch(params.get(0), null,
                origin + ":splitElement:receiver");
        if (receiver.sort != Sort.STRING) {
            return codecGap("splitElement", "NON_STRING_PARAMETER", origin,
                    Sort.STRING);
        }
        if (nullnessUnknown(Collections.singletonList(receiver))) {
            return refuse(Reason.JAVA_STRING_NULLNESS_UNKNOWN, origin,
                    "splitElement", Sort.STRING);
        }
        String s = receiver.text;
        String d = VmExpressionIr.quote(String.valueOf(delimiter));
        List<String> at = new ArrayList<String>();
        at.add("(- 1)");
        for (int k = 1; k <= index + 1; k++) {
            String previous = at.get(k - 1);
            at.add(k == 1 ? "(str.indexof " + s + " " + d + " 0)"
                    : "(ite (< " + previous + " 0) (- 1) (str.indexof " + s
                    + " " + d + " (+ " + previous + " 1)))");
        }
        String length = "(str.len " + s + ")";
        String begin = index == 0 ? "0" : "(+ " + at.get(index) + " 1)";
        String next = at.get(index + 1);
        String end = "(ite (< " + next + " 0) " + length + " " + next + ")";
        String rest = "(str.substr " + s + " " + begin + " (- " + length
                + " " + begin + "))";
        String exists = "(ite (< " + at.get(1) + " 0) "
                + (index == 0 ? "true" : "false") + " " + and(Arrays.asList(
                index == 0 ? "true" : "(>= " + at.get(index) + " 0)",
                "(not (str.in_re " + rest + " (re.* (str.to_re " + d
                        + "))))")) + ")";
        return Term.nonNullString("(str.substr " + s + " " + begin + " (- "
                + end + " " + begin + "))", and(Arrays.asList(
                stringDefinedness(Collections.singletonList(receiver),
                        Collections.<Term>emptyList()), exists)));
    }

    private Term stringPosition(String operation, JsonArray params,
                                String origin) {
        boolean charAt = "charAt".equals(operation);
        if (params.size() != 2 && (charAt || params.size() != 3)) {
            return codecGap(operation, "ARITY", origin, Sort.INT);
        }
        Term receiver = dispatch(params.get(0), null,
                origin + ":" + operation + ":receiver");
        Term argument = dispatch(params.get(1), null,
                origin + ":" + operation + ":argument");
        Term from = params.size() == 3 ? dispatch(params.get(2), Sort.INT,
                origin + ":" + operation + ":from") : null;
        if (receiver.sort != Sort.STRING || (argument.sort != Sort.INT
                && (charAt || argument.sort != Sort.STRING))
                || from != null && from.sort != Sort.INT) {
            return codecGap(operation, "PARAMETER_SORT", origin, Sort.INT);
        }
        if (nullnessUnknown(Arrays.asList(receiver, argument))) {
            return refuse(Reason.JAVA_STRING_NULLNESS_UNKNOWN, origin,
                    operation, Sort.INT);
        }
        String text = receiver.text;
        String length = "(str.len " + text + ")";
        if (charAt) {
            String index = argument.text;
            String code = "(str.to_code (str.at " + text + " " + index + "))";
            return definedResult(code, Sort.INT, IntegralWidth.JAVA_INT,
                    and(Arrays.asList(stringDefinedness(
                                    Collections.singletonList(receiver),
                                    Collections.singletonList(argument)),
                            "(<= 0 " + index + ")",
                            "(< " + index + " " + length + ")")));
        }
        boolean character = argument.sort == Sort.INT;
        String needle = character ? codePoint(argument.text) : argument.text;
        List<Term> evaluated = new ArrayList<Term>();
        if (character) evaluated.add(argument);
        if (from != null) evaluated.add(from);
        String defined = stringDefinedness(character
                ? Collections.singletonList(receiver)
                : Arrays.asList(receiver, argument), evaluated);
        String found = "indexOf".equals(operation)
                ? firstIndex(text, needle, from)
                : lastIndex(text, needle, from);
        String valid = character ? validCodePoint(argument.text) : "true";
        return definedResult("true".equals(valid) ? found
                        : "(ite " + valid + " " + found + " (- 1))", Sort.INT,
                IntegralWidth.JAVA_INT, defined);
    }

    private static String firstIndex(String text, String needle, Term from) {
        if (from == null) return "(str.indexof " + text + " " + needle + " 0)";
        String length = "(str.len " + text + ")";
        return "(ite (< " + length + " " + from.text + ") (ite (= " + needle
                + " \"\") " + length + " (- 1)) (str.indexof " + text + " "
                + needle + " (ite (< " + from.text + " 0) 0 " + from.text
                + ")))";
    }

    private String lastIndex(String text, String needle, Term from) {
        String last = symbols.mint("last_index_of__",
                scope + "#" + lastIndexes++, 10);
        declare(last, Sort.INT);
        String size = "(str.len " + needle + ")";
        String right = "(- (str.len " + text + ") " + size + ")";
        String bound = from == null ? right : "(ite (< " + from.text + " "
                + right + ") " + from.text + " " + right + ")";
        String reached = from == null ? "true" : "(<= 0 " + from.text + ")";
        sideCondition(or(Arrays.asList(
                from == null ? "false" : "(and (< " + from.text + " 0) (= "
                        + last + " (- 1)))",
                and(Arrays.asList(reached, "(= " + size + " 0)", "(= " + last
                        + " " + bound + ")")),
                and(Arrays.asList(reached, "(< 0 " + size + ")", "(= " + last
                        + " (- 1))", "(or (< " + bound + " 0) (not "
                        + "(str.contains (str.substr " + text + " 0 (+ "
                        + bound + " " + size + ")) " + needle + ")))")),
                and(Arrays.asList(reached, "(< 0 " + size + ")", "(<= 0 "
                        + last + ")", "(<= " + last + " " + bound + ")",
                        "(= (str.substr " + text + " " + last + " " + size
                                + ") " + needle + ")",
                        "(not (str.contains (str.substr " + text + " (+ "
                                + last + " 1) (- (+ " + bound + " " + size
                                + ") (+ " + last + " 1))) " + needle
                                + "))")))));
        return last;
    }

    private static String codePoint(String c) {
        if (c.matches("[0-9]+") && Long.parseLong(c) < 65536L) {
            return "(str.from_code " + c + ")";
        }
        String offset = "(- " + c + " 65536)";
        return "(ite (< " + c + " 65536) (str.from_code " + c + ") (str.++ "
                + "(str.from_code (+ 55296 (div " + offset + " 1024))) "
                + "(str.from_code (+ 56320 (mod " + offset + " 1024)))))";
    }

    private static String validCodePoint(String c) {
        if (c.matches("[0-9]+")) {
            return Long.parseLong(c) <= 1114111L ? "true" : "false";
        }
        return VmTermLowering.integralRange("0", c, "1114111");
    }

    private Term compareTo(JsonArray params, String origin) {
        StringParameters strings = stringParameters(params, 2, "compareTo",
                origin, Sort.INT);
        if (strings.terms == null) return strings.refusal;
        String one = strings.terms.get(0).text;
        String other = strings.terms.get(1).text;
        String oneLength = "(str.len " + one + ")";
        String otherLength = "(str.len " + other + ")";
        String shorter = "(ite (<= " + oneLength + " " + otherLength + ") "
                + oneLength + " " + otherLength + ")";
        String at = symbols.mint("compare_at__", scope + "#" + comparisons++,
                10);
        declare(at, Sort.INT);
        String oneChar = "(str.at " + one + " " + at + ")";
        String otherChar = "(str.at " + other + " " + at + ")";
        sideCondition(and(Arrays.asList("(<= 0 " + at + ")", "(<= " + at
                        + " " + shorter + ")", "(= (str.substr " + one + " 0 " + at
                        + ") (str.substr " + other + " 0 " + at + "))",
                "(or (= " + at + " " + shorter + ") (not (= " + oneChar + " "
                        + otherChar + ")))")));
        return definedResult("(ite (= " + at + " " + shorter + ") (- "
                        + oneLength + " " + otherLength + ") (- (str.to_code "
                        + oneChar + ") (str.to_code " + otherChar + ")))",
                Sort.INT, IntegralWidth.JAVA_INT, strings.defined);
    }

    private int comparisons;

    private int lastIndexes;

    private static String truth(StringIdentities.BooleanTest test, Term flag) {
        return test.truth == StringIdentities.Truth.FLAG ? flag.text
                : test.truth == StringIdentities.Truth.NEGATED
                ? "(not " + flag.text + ")" : "false";
    }

    private Term stringEquals(JsonArray params, boolean negated,
                              String origin) {
        if (params.size() != 2) {
            return codecGap("equals", "ARITY", origin, Sort.BOOL);
        }
        Term receiver = dispatch(params.get(0), null,
                origin + ":equals:parameter0");
        Term argument = enumOperand(params.get(1),
                origin + ":equals:parameter1");
        if (receiver.sort != Sort.STRING) {
            return codecGap("equals", "NON_STRING_PARAMETER", origin,
                    Sort.BOOL);
        }
        if (nullnessUnknown(Collections.singletonList(receiver))) {
            return refuse(Reason.JAVA_STRING_NULLNESS_UNKNOWN, origin,
                    "equals:0", Sort.BOOL);
        }
        String predicate;
        if (argument.isNullReference()) {
            predicate = "false";
        } else if (argument.sort != Sort.STRING) {
            return codecGap("equals", "ARGUMENT_DYNAMIC_TYPE_UNMODELED",
                    origin, Sort.BOOL);
        } else if (argument.stringNullness.isEmpty()) {
            return refuse(Reason.JAVA_STRING_NULLNESS_UNKNOWN, origin,
                    "equals:1", Sort.BOOL);
        } else {
            predicate = and(Arrays.asList(stringNonNull(argument),
                    renderedEquality(params, origin, "(= " + receiver.text
                            + " " + argument.text + ")")));
        }
        return booleanStringResult(predicate, negated, stringDefinedness(
                Collections.singletonList(receiver),
                Collections.singletonList(argument)));
    }

    private Term startsWithAt(JsonArray params, boolean negated,
                              String origin) {
        JsonArray strings = new JsonArray();
        strings.add(params.get(0));
        strings.add(params.get(1));
        StringParameters both = stringParameters(strings, 2, "startsWith",
                origin, Sort.BOOL);
        if (both.terms == null) return both.refusal;
        Term offset = dispatch(params.get(2), Sort.INT,
                origin + ":startsWith:offset");
        if (offset.sort != Sort.INT) {
            return codecGap("startsWith", "NON_INT_PARAMETER", origin,
                    Sort.BOOL);
        }
        String text = both.terms.get(0).text;
        String length = "(str.len " + text + ")";
        String at = offset.text;
        return booleanStringResult(and(Arrays.asList("(<= 0 " + at + ")",
                "(<= " + at + " " + length + ")", "(str.prefixof "
                        + both.terms.get(1).text + " (str.substr " + text + " "
                        + at + " (- " + length + " " + at + ")))")), negated,
                and(Arrays.asList(both.defined, offset.precondition)));
    }

    private Term regionMatches(JsonArray params, boolean negated,
                               String origin) {
        String operation = "regionMatches";
        int first = params.size() - 4;
        if (first != 1 && first != 2) {
            return codecGap(operation, "ARITY", origin, Sort.BOOL);
        }
        if (first == 2 && !"false".equals(dispatch(params.get(1), null,
                origin + ":" + operation + ":ignoreCase").text)) {
            return codecGap(operation, "IGNORE_CASE", origin, Sort.BOOL);
        }
        JsonArray strings = new JsonArray();
        strings.add(params.get(0));
        strings.add(params.get(first + 1));
        StringParameters both = stringParameters(strings, 2, operation,
                origin, Sort.BOOL);
        if (both.terms == null) return both.refusal;
        List<Term> ints = new ArrayList<Term>();
        for (int index : new int[] {first, first + 2, first + 3}) {
            Term value = dispatch(params.get(index), Sort.INT,
                    origin + ":" + operation + ":parameter" + index);
            if (value.sort != Sort.INT) {
                return codecGap(operation, "NON_INT_PARAMETER", origin,
                        Sort.BOOL);
            }
            ints.add(value);
        }
        String one = both.terms.get(0).text;
        String other = both.terms.get(1).text;
        String at = ints.get(0).text;
        String otherAt = ints.get(1).text;
        String count = ints.get(2).text;
        return booleanStringResult(and(Arrays.asList("(<= 0 " + at + ")",
                "(<= 0 " + otherAt + ")", "(<= " + at + " (- (str.len " + one
                        + ") " + count + "))", "(<= " + otherAt
                        + " (- (str.len " + other + ") " + count + "))",
                "(or (<= " + count + " 0) (= (str.substr " + one + " " + at
                        + " " + count + ") (str.substr " + other + " "
                        + otherAt + " " + count + ")))")), negated,
                stringDefinedness(both.terms, ints));
    }

    private String renderedEquality(JsonArray params, String origin,
                                    String text) {
        StringIdentities.BooleanTest test =
                StringIdentities.booleanTest(params, false);
        if (test != null) {
            Term flag = dispatch(test.flag, null, origin + ":equals:flag");
            return flag.sort == Sort.BOOL ? truth(test, flag) : text;
        }
        List<StringIdentities.Part[]> pairs = StringIdentities.pieceWise(
                params.get(0), params.get(1));
        if (pairs == null) return text;
        List<String> equalities = new ArrayList<String>();
        for (StringIdentities.Part[] pair : pairs) {
            boolean string = pair[0].kind == StringIdentities.Kind.STR;
            Term one = dispatch(string ? pair[0].node : pair[0].operand, null,
                    origin + ":equals:piece");
            Term other = dispatch(string ? pair[1].node : pair[1].operand,
                    null, origin + ":equals:piece");
            Sort sort = string ? Sort.STRING
                    : pair[0].kind == StringIdentities.Kind.BOOL ? Sort.BOOL
                    : Sort.INT;
            if (one.sort != sort || other.sort != sort) return text;
            equalities.add("(= " + one.text + " " + other.text + ")");
        }
        return and(equalities);
    }

    private StringParameters stringParameters(JsonArray params, int arity,
                                              String operation,
                                              String origin,
                                              Sort resultSort) {
        if (params.size() != arity) {
            return new StringParameters(null, codecGap(operation, "ARITY",
                    origin, resultSort));
        }
        List<Term> result = new ArrayList<>();
        for (int index = 0; index < params.size(); index++) {
            Term value = dispatch(params.get(index), null,
                    origin + ":" + operation + ":parameter" + index);
            if (value.sort != Sort.STRING) {
                return new StringParameters(null, codecGap(operation,
                        "NON_STRING_PARAMETER", origin, resultSort));
            }
            result.add(value);
        }
        if (nullnessUnknown(result)) {
            return new StringParameters(null, refuse(
                    Reason.JAVA_STRING_NULLNESS_UNKNOWN, origin, operation,
                    resultSort));
        }
        return new StringParameters(result, null);
    }

    private static final class StringParameters {
        private final List<Term> terms;
        private final Term refusal;
        private final String defined;

        private StringParameters(List<Term> terms, Term refusal) {
            this.terms = terms;
            this.refusal = refusal;
            this.defined = terms == null ? "" : stringDefinedness(terms,
                    Collections.<Term>emptyList());
        }
    }

    private static Term booleanStringResult(String predicate,
                                            boolean negated,
                                            String definedness) {
        return definedResult(negated ? "(not " + predicate + ")" : predicate,
                Sort.BOOL, IntegralWidth.NONE, definedness);
    }

    private static String stringNonNull(Term term) {
        if (term.sort != Sort.STRING) return "false";
        return "false".equals(term.stringNullness) ? "true"
                : "(not " + term.stringNullness + ")";
    }

    private Term codecGap(String operation, String gap, String origin,
                          Sort sort) {
        return refuse(Reason.MODEL_SEMANTICS_MISSING, origin,
                "OpStrExpression." + operation + ":" + gap, sort);
    }


    private static Term fromValue(Term value, String javaType) {
        if (value.sort != Sort.VALUE) return value;
        String kind = ContainerStateModel.unboxableCellKind(javaType);
        if (kind.isEmpty()) return value;
        String defined = and(Arrays.asList(value.precondition,
                "((_ is " + kind + ") " + value.text + ")"));
        String integral = ContainerStateModel.unboxIntegral(value.text,
                javaType);
        if (!integral.isEmpty()) {
            return definedResult(integral, Sort.INT,
                    JavaPrimitiveSmtSemantics.widthOfJavaType(javaType),
                    defined);
        }
        if ("VBool".equals(kind)) {
            return definedResult("(valueBool " + value.text + ")",
                    Sort.BOOL, IntegralWidth.NONE, defined);
        }
        if ("VFloat".equals(kind)) {
            return definedResult("(valueFloat " + value.text + ")",
                    Sort.FLOAT32, IntegralWidth.NONE, defined);
        }
        if ("VDouble".equals(kind)) {
            return definedResult("(valueDouble " + value.text + ")",
                    Sort.FLOAT64, IntegralWidth.NONE, defined);
        }
        if ("VString".equals(kind)) {
            return Term.nonNullString("(valueString " + value.text + ")",
                    defined);
        }
        return value;
    }


    private static IntegralWidth promotedIntegralWidth(Term left,
                                                       Term right) {
        if (left.sort != Sort.INT || right.sort != Sort.INT) {
            return IntegralWidth.NONE;
        }
        return JavaPrimitiveSmtSemantics.promote(left.integralWidth,
                right.integralWidth);
    }

    private static String stringLiteral(JsonElement expression) {
        return VmExpressionIr.exactStringLiteral(expression,
                type -> JavaSmtSorts.sortOfJava(type) == Sort.STRING);
    }

    private Term floatingPromotion(Term term, Sort target,
                                  String origin) {
        FloatingKind targetKind = floatingKind(target);
        if (term.sort == target) return term;
        if (term.sort.floating()) {
            String converted = JavaPrimitiveSmtSemantics.floatingConversion(
                    term.text, floatingKind(term.sort), targetKind);
            if (converted != null) {
                return dependent(Term.of(converted, target), term);
            }
        } else if (term.sort == Sort.INT
                && term.integralWidth != IntegralWidth.NONE) {
            String converted = JavaPrimitiveSmtSemantics.integralToFloating(
                    term.text, targetKind);
            if (converted != null) {
                return dependent(Term.of(converted, target), term);
            }
        }
        return refuse(Reason.UNSUPPORTED_JAVA_NUMERIC_PROMOTION,
                origin, term.sort + "->" + target, target);
    }

    private Term typeCast(JsonObject expression,
                         String origin) {
        JsonElement sourceExpression = expression.get("_exp");
        Term source = dispatch(sourceExpression, null,
                origin + ":castSource");
        String sourceType = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                firstNonBlank(optionalString(expression, "sourceJavaType"),
                        expressionJavaType(sourceExpression)));
        String targetType = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                firstNonBlank(optionalString(expression, "targetJavaType"),
                        optionalString(expression, "_java_type")));
        Sort sourceSort = JavaSmtSorts.castSort(sourceType);
        Sort targetSort = JavaSmtSorts.castSort(targetType);
        Sort refused = targetSort == Sort.VALUE ? Sort.REF : targetSort;
        boolean primitivePair = JavaPrimitiveSmtSemantics
                .primitiveNumericDescriptor(sourceType)
                && JavaPrimitiveSmtSemantics
                .primitiveNumericDescriptor(targetType);
        if (source != null && primitivePair && source.sort == sourceSort) {
            String conversion = JavaPrimitiveSmtSemantics.primitiveCast(
                    source.text, sourceType, targetType);
            if (conversion != null) {
                return dependent(Term.of(conversion, targetSort,
                        JavaPrimitiveSmtSemantics.widthOfJavaType(
                                targetType)), source);
            }
        } else if (source != null && primitivePair) {
            return refuse(Reason.JAVA_CAST_SOURCE_SORT_CONFLICT,
                    origin, firstNonBlank(sourceType, "UNKNOWN") + ":"
                            + source.sort + "!=" + sourceSort, refused);
        }
        return refuse(Reason.UNSUPPORTED_JAVA_CAST, origin,
                firstNonBlank(sourceType, "UNKNOWN") + "->"
                        + firstNonBlank(targetType, "UNKNOWN"), refused);
    }

    private static <K> void add(Map<K, Set<String>> index, K key,
                                String symbol) {
        index.computeIfAbsent(key, held -> new LinkedHashSet<String>())
                .add(symbol);
    }
}
