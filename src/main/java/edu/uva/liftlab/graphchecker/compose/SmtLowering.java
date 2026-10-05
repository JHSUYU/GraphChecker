package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Reason;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Term;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
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
import java.util.function.BiPredicate;
import java.util.function.Supplier;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.and;
import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.expressionJavaType;
import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.floatingKind;
import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.numeric;
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

/**
 * The ONE SMT lowering, shared by the composer and the flip solver so the
 * two queries cannot disagree about a projection, a cell width or a root's
 * name.  It states once what a leaf may be, what a read joins to, and where
 * a definedness fact is conjoined.
 *
 * <p>A leaf is one of: a DECLARED symbol (root, handoff v_H, clock cell),
 * lowered to its published name since pi and phi are written over it; an
 * execution-local IDENTITY, opaque, per session, non-null and distinct
 * within its session; a literal or a container relation over those.
 * Anything else is refused as the propagation cut, never minted free.</p>
 */
public final class SmtLowering {

    /** The refusal that means "propagation did not carry the value". */
    public static final String CUT = "PROPAGATION_CUT";
    /** The refusal that means "the recording states no value here". */
    public static final String UNSTATED = "UNSTATED_VALUE";
    /** The refusal that means "one solver name, two sorts". */
    public static final String SORT_CONFLICT = "SORT_CONFLICT";
    /** How a published term names an expression of the session's table. */
    static final String REFERENCE = "EXPR.";
    /** How deep a reference may stand for text naming another reference. */
    private static final int REFERENCE_ROUNDS = 4;

    /**
     * The write log of one session, as the state join reads it.  Joins stay
     * within the session: versions are session-local counters.
     */
    public interface SessionJoin {
        /** The write expression at this location and version, or null. */
        JsonElement writeExpression(String locationKey, long version);

        /** This session's writes of one location, in the order it wrote. */
        List<WriteRow> writes(String locationKey);

        /** This session's reads of one location, in the order it read. */
        List<ReadRow> reads(String locationKey);

        /**
         * The symbols this session's placeholder rows state for the version
         * a mint created.  No {@code WriteRow} states that version, so rows
         * are matched by {@code ReadRow.mintVersion} (CONTRACT v2.4), which
         * is unique; {@code (occurrence, location)} is not, since one
         * occurrence may declare one cell under several ports.
         */
        Set<String> mintedReadSymbols(long version);

        /**
         * The symbols this session's read rows state for one location at one
         * version.  The join inlines the writer's propagation, so a
         * container's read symbol appears nowhere in the text; this is how
         * {@code Corpus#expressionSymbols} names the recorded state a
         * container read rests on.
         *
         * <p>Placeholder rows are excluded: their {@code observedVersion} is
         * the write they were laid over, so listing them here would put the
         * minted value on that write's readers.</p>
         */
        Set<String> readSymbols(String locationKey, long version);

        /**
         * Whether a witness may move this recorded symbol's value: a root or
         * a clock cell this session minted or read, or a value it received
         * (a handoff's v_H, which a MESSAGE family binds).
         */
        boolean moves(String symbol);

        /**
         * Whether the stage this join lowers for may re-pair this read --
         * the read event {@code readEvent} ({@link VmRows#readEvent}, its
         * row's seq) of this location -- with another writer, so a value
         * resting on it can move ({@link #moves}): in a composition, the
         * anchor's reads a STATE family re-pairs; in a flip query, every
         * read of a location some write row states, each taking one of its
         * eligible writers ({@link #repairing}).  None in a join no stage
         * opened.
         */
        boolean repaired(String locationKey, long readEvent);

        /**
         * Whether a writer occurrence of this session may have run before a
         * reader in another schedule of it: HB-concurrent
         * ({@code Arms#concurrent}); never in a join no composition opened.
         */
        boolean concurrent(OccurrenceAddress reader,
                           OccurrenceAddress writer);

        /** The occurrence of this session that computed on an arrival it
         *  refused ({@link RefusalFrame}), or null. */
        default RefusalFrame frame(String occurrenceId) {
            return null;
        }

        /** The frame whose occurrence wrote this version of this location
         *  (no INITIAL), or null: indexed once per session. */
        default RefusalFrame frameOfWrite(String locationKey, long version) {
            return null;
        }
    }

    /**
     * A FRAME: an occurrence whose run refused an arrival (the VM refused
     * the attach, {@code runtime.WireExport}) and computed on it as a
     * constant, so every value it wrote may rest on what made the arrival.
     * Its producer is the export the refused attach's VM handle names in
     * this session ({@link ExportRow#handle}); what that export rests on
     * that can move is {@link #frameMovers}'s, the one predicate every pin
     * asks ({@link #movers}).  No export row of the session stating the
     * handle: its producer unstated, so its values are held.
     */
    public static final class RefusalFrame {
        /** The producers' endpoint ids, or "" where no row states one. */
        public final String producer;
        /** The producers' export expressions. */
        final List<JsonElement> exports;
        /** The refusal its row states. */
        public final String refusal;

        RefusalFrame(String producer, List<JsonElement> exports,
                     String refusal) {
            this.producer = producer;
            this.exports = Collections.unmodifiableList(exports);
            this.refusal = refusal;
        }
    }

    /** What a frame's producer exports rest on that can move ({@link
     *  #movers}, under the open join): empty, its values hold. */
    public Set<String> frameMovers(RefusalFrame frame) {
        Set<String> moving = new LinkedHashSet<String>();
        for (JsonElement export : frame.exports) {
            moving.addAll(movers(export, true));
        }
        return moving;
    }

    /** The leaves a frame's write was freed to ({@link Binder#framed}):
     *  no plant reaches them, so a flip resting only on them is refused
     *  before it is solved ({@code explore.FlipQuery}). */
    public Set<String> framedLeaves() {
        return Collections.unmodifiableSet(framedLeaves);
    }

    /** How a refused attach's row names the VM handle it refused
     *  ({@code runtime.WireExport#refused}). */
    private static final Pattern REFUSED_HANDLE =
            Pattern.compile("refused the attach of handle ([0-9]+)");

    /** The join of no session: it states nothing. */
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

    /**
     * The same join, where the stage may re-pair the reads {@code repaired}
     * accepts, by location and read event: a composition's, the anchor's
     * reads a STATE family re-pairs ({@code Composer}, each {@link #readKey})
     * and no other -- another occurrence's read of the same location keeps
     * the run's pairing; a flip query's, every read of a location with write
     * rows ({@link #forSession}) -- and where this session's occurrences are
     * ordered as {@code concurrent} says.
     */
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
        };
    }

    /** One read of one location, as {@link #repairing} and {@link #movable}
     *  name it: its location and its event ({@link VmRows#readEvent}). */
    public static String readKey(String locationKey, long readEvent) {
        return locationKey + "#e" + readEvent;
    }

    /**
     * The one symbol the mint at this version gave the read: {@code ""} when
     * no row states one, {@code null} when rows disagree (the recording
     * contradicts itself; callers refuse it by name).
     */
    public static String mintedReadSymbol(SessionJoin join, long version) {
        if (version < 0L) return "";
        Set<String> symbols = join.mintedReadSymbols(version);
        if (symbols.isEmpty()) return "";
        if (symbols.size() > 1) return null;
        return symbols.iterator().next();
    }

    private final SmtSymbolTable symbols = new SmtSymbolTable();
    /**
     * Every name this query gives a meaning to: ONE registry for both what
     * the recording states and what the query declares ({@link #declare}).
     * Two registries would cut a leaf as free while its name is bound.
     */
    private final Map<String, Declared> declarations =
            new LinkedHashMap<String, Declared>();
    /**
     * Everything this lowering states, as {@link Stated}: FACTS about a name
     * (non-null identity, integral domain, cell shape) and LABELED questions
     * for the composition's unsat core.  Other callers take only the facts
     * ({@link #facts}).
     */
    private final List<Stated> assertions = new ArrayList<Stated>();
    private final Set<String> assertedOnce = new LinkedHashSet<String>();
    /** Declared symbols this lowering actually put in the formula. */
    private final Set<String> usedSymbols = new LinkedHashSet<String>();
    /** Session -> its objects, by the rid the VM gave them. */
    private final Map<String, Map<Long, String>> recordedObjects =
            new LinkedHashMap<String, Map<Long, String>>();
    private final Map<String, String> opaqueIdentities =
            new LinkedHashMap<String, String>();
    private final Map<String, SharedTerm> sharedTerms =
            new LinkedHashMap<String, SharedTerm>();
    /**
     * The same subterms by the name they were minted under;
     * {@link #sharedTerms} is keyed by definition digest for dedupe.
     */
    private final Map<String, SharedTerm> sharedByName =
            new LinkedHashMap<String, SharedTerm>();
    private final Map<String, String> unsupportedDetail =
            new LinkedHashMap<String, String>();
    /**
     * The reads {@code Composer#pin} bound to what their row states, as
     * {@code session|symbol}: a guarded read of their version that does not
     * join lowers to its symbol (PIN, {@link #guardedReadTerm}).
     */
    private final Set<String> pins = new LinkedHashSet<String>();
    /** {@link #framedLeaves}. */
    private final Set<String> framedLeaves = new LinkedHashSet<String>();
    /**
     * The reads a STATE family of the path being composed may bind to
     * another writer's value, as {@code session|}{@link #readKey}
     * ({@link #movable}, {@link #path}): what is asked through one is asked
     * of the object it is ({@link #perCandidate}).
     */
    private final Set<String> movable = new LinkedHashSet<String>();
    /** {@code session|location|class} -> {@link #candidates}. */
    private final Map<String, Map<Long, Candidate>> candidates =
            new HashMap<String, Map<Long, Candidate>>();
    /**
     * {@code session|read symbol|version of the store} -> the states of the
     * object that store delivers a query through the read may see, by their
     * nested selectors ({@link #storeChoice}, {@link #stateChoices}).
     */
    private final Map<String, Map<String, WriteRow>> storeStates =
            new HashMap<String, Map<String, WriteRow>>();
    /** {@code session|read symbol} -> the reads queries through it answered
     *  ({@link #askedThrough}). */
    private final Map<String, Set<ReadRow>> askedThrough =
            new HashMap<String, Set<ReadRow>>();
    /** The nested selectors the path being composed minted, in any scope
     *  ({@link #nestedSelectors}). */
    private final Set<String> nestedSelectors = new LinkedHashSet<String>();
    /** The reads whose joined value is being lowered, innermost first: the
     *  read a container query answers ({@link #query}). */
    private final Deque<ReadAt> answering = new ArrayDeque<ReadAt>();
    private final Set<String> integralDomains = new LinkedHashSet<String>();

    /**
     * Where a symbol's declaration comes from.  A CORPUS lowering knows every
     * declared symbol, so an undeclared scalar leaf is the propagation cut.
     * A SESSION lowering sees one expression, so the leaf's own
     * {@code _java_type} declares it.  The lowering itself is the same.
     */
    private final boolean symbolsDeclareThemselves;
    /** The session's expression table, for {@link #lower(String)}. */
    private final ExpressionTable table;

    /** What the conjunction now open raised: its frame of {@link #raising}. */
    private Raised open;
    private String scope = "";
    /** The arm whose body is open ({@link #arm}), "" for a path's. */
    private String arm = "";
    /** Session -> clock symbol -> its base there ({@link #clockBases}). */
    private Map<String, Map<String, Long>> clockBases =
            Collections.emptyMap();
    private SessionJoin join = NO_JOIN;
    /** The expression table of the session whose conjunction is open. */
    private ExpressionTable openTable;
    /** The conjunctions a nested lowering interrupted, innermost first. */
    private final Deque<Frame> frames = new ArrayDeque<Frame>();
    /**
     * THE MEMO: what each node of the decoder-owned expression DAG lowered
     * to, per expected sort, with the refusals its lowering raised.  A node
     * is reached along every path to it; walked again, the chain beneath it
     * was lowered again (a Solr cluster state rebuilt per notification:
     * millions of terms), and a refused leaf minted a fresh name at each
     * visit, so no subterm above it deduplicated.  One conjunction has one
     * memo ({@link #begin}).  An entry holds while the declarations it read
     * stand; a name newly stated clears the memo ({@link #put}).
     */
    private Map<MemoKey, Attempt<?>> memo = new HashMap<MemoKey, Attempt<?>>();
    /** The memo keys whose lowering is in progress ({@link #memoized}). */
    private final Set<MemoKey> lowering = new HashSet<MemoKey>();
    /**
     * The nodes a {@link #moves} walk of this conjunction found resting on
     * nothing that moves, so no later walk of it goes through them again.
     */
    private Set<JsonElement> still = identities();
    /**
     * What {@link ContainerSmtCodec}'s walk found of each chain node of this
     * conjunction: whether it stands on a stated base.  A chain resolves
     * through the open join, so the answer is the conjunction's.
     */
    private Map<JsonElement, Boolean> statedBases = statedBases();
    /**
     * THE FRAMES, innermost last (null while one raised nothing): what each
     * lowering in progress raised ({@link Raised}).  Anything is raised into
     * the innermost only, and reaches the one enclosing it only when
     * {@link #commit}ted.  The open conjunction is a frame ({@link #begin});
     * a memoized lowering is committed on every hit; an attempt (a join,
     * {@link #bind}) is committed or dropped, and dropped it raised NOTHING --
     * no refusal, no side condition, no gap.  No other route puts anything
     * on a path: a path-level list filled at once kept a join's refusals
     * after its pin bound the read and missed a memo hit's (SOLR-18406 s46),
     * and a dropped writer's recorded readings and container requires still
     * bound the path.
     */
    private final List<Raised> raising = new ArrayList<Raised>();
    /**
     * What reached no frame: this lowering's own.  A side condition here is
     * a FACT ({@link #assertPlain}, as when no conjunction is open), a
     * diagnostic the corpus's gap; a refusal refuses nothing.
     */
    private final Raised root = new Raised();

    /** The lowering of one CORPUS: its rows declare every symbol. */
    public SmtLowering(Map<String, Sort> declaredSymbols) {
        this(declaredSymbols, false, null);
    }

    private SmtLowering(Map<String, Sort> declaredSymbols,
                        boolean symbolsDeclareThemselves,
                        ExpressionTable table) {
        // Stated by the corpus, not yet in the query: a name joins the
        // query (and the preamble) only when the formula names it.
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

    /**
     * One name's declaration.  {@code stated}: the recording gives it a
     * meaning, so a leaf naming it is not cut.  {@code inQuery}: the formula
     * names it, so the preamble declares it.
     */
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

    /**
     * The lowering of ONE session's expressions, by reference, with its
     * write log (the flip solver's entry; same lowering as the composer's).
     * A flip query re-pairs every read of a location some write row states
     * among its eligible writers ({@code FlipQuery}'s writer choice), so a
     * value resting on such a read can move: no pin stands for it.
     */
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

    /**
     * One session's write log and read rows, as the state join reads them;
     * the only implementation, built once per session ({@code Corpus#join}).
     */
    public static SessionJoin joinOf(final SessionReader session) {
        final Map<String, String> writes = new LinkedHashMap<String, String>();
        final Map<String, List<WriteRow>> byLocation =
                new LinkedHashMap<String, List<WriteRow>>();
        for (WriteRow write : session.writes()) {
            String key = locationKey(write.location());
            writes.put(key + "#" + write.version(), write.expressionRef());
            byLocation.computeIfAbsent(key, held -> new ArrayList<WriteRow>())
                    .add(write);
        }
        final Map<String, List<ReadRow>> readsOf =
                new LinkedHashMap<String, List<ReadRow>>();
        // A row's symbol counts when it states one (its JOIN or PIN binds
        // it): by mint version, else by the location and version it saw.
        final Map<Long, Set<String>> minted =
                new LinkedHashMap<Long, Set<String>>();
        final Map<String, Set<String>> observed =
                new LinkedHashMap<String, Set<String>>();
        // What a witness may move: the roots and clock cells this session
        // minted or read, and the values it received.
        final Set<String> moving = new LinkedHashSet<String>();
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
                add(observed, locationKey(read.location()) + "#"
                        + read.observedVersion(), read.symbol());
            }
        }
        final Map<String, RefusalFrame> frames = frames(session);
        // Location#version -> the frame whose occurrence wrote it.
        final Map<String, RefusalFrame> framedWrites =
                new HashMap<String, RefusalFrame>();
        for (WriteRow write : session.writes()) {
            RefusalFrame frame = write.initial() ? null
                    : frames.get(write.endpoint().occurrence().id());
            if (frame != null) {
                framedWrites.put(locationKey(write.location()) + "#"
                        + write.version(), frame);
            }
        }
        return new SessionJoin() {
            @Override
            public JsonElement writeExpression(String locationKey,
                                               long version) {
                String ref = writes.get(locationKey + "#" + version);
                return ref == null ? null
                        : session.expressions().expression(ref);
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
                Set<String> symbols =
                        observed.get(locationKey + "#" + version);
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
                return framedWrites.get(locationKey + "#" + version);
            }
        };
    }

    /**
     * The frames of one session ({@link RefusalFrame}): each occurrence an
     * UNSTATED_VALUE row of it is filed on (a refused attach, an attach
     * that minted no boundary variable), with the producers its refused
     * attaches' handles name through the session's exports, and their
     * export expressions.  A row naming no occurrence is no frame.
     */
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
        for (GapRow gap : session.gaps()) {
            if (gap.kind() != GapKind.UNSTATED_VALUE) continue;
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

    /**
     * One expression of this session, lowered to text, or a named refusal;
     * {@link #reference} is the rule, so its definedness is a fact of this
     * lowering ({@link #facts}).  Callers ask {@link #declaredSort} for
     * the names it reaches.
     */
    public Lowered lower(String expressionRef) {
        Attempt<Term> lowered = attempting(
                () -> reference(expressionRef, "lower:" + expressionRef));
        Term value = commit(lowered);
        if (value == null) {
            return Lowered.refused("ABSENT_EXPRESSION:" + expressionRef);
        }
        return new Lowered(value.text, value, lowered);
    }

    /**
     * One published term (a decision's or phi) as {@link #statedTerm}
     * lowers it, with what it reaches ({@link Lowered#reach}): the
     * closure's question about a term.
     */
    public Lowered lowerTerm(String term, String origin) {
        Attempt<String> lowered = attempting(() -> statedTerm(term, origin));
        String text = commit(lowered);
        return text.isEmpty() ? Lowered.refused("UNSTATED_TERM:" + origin)
                : new Lowered(text, null, lowered);
    }

    /**
     * One expression of the open conjunction's session, by {@link
     * #reference}: its definedness is a side condition of that conjunction,
     * answered by {@link #end} with the rest.  Null when the table lacks it.
     */
    public Term term(String expressionRef, String origin) {
        return reference(expressionRef, origin);
    }

    /**
     * One published term (pi or phi) with every {@code EXPR.<ref>} it names
     * lowered through the same routine as deliveries, so pi, phi and the
     * deliveries share one vocabulary.  Treating a reference as a free name
     * would put the propagation outside the formula.
     *
     * <p>Answers "" on refusal; the caller must then drop the whole
     * conjunct.</p>
     */
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

    /**
     * One pass: every reference token of this text, lowered in place; ""
     * at the first that refuses, lowering none after it.
     */
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

    /** One reference of a published term, lowered by {@link #reference}. */
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

    /**
     * THE rule for one expression reference: lowered in the open session's
     * scope (this lowering's own table when none is open), its definedness
     * conjoined, since the JVM evaluated it: a side condition of the open
     * conjunction, else a fact of this lowering.  Null when the table does
     * not hold the reference.
     */
    private Term reference(String reference, String origin) {
        ExpressionTable expressions = openTable == null ? table : openTable;
        JsonObject expression = reference == null ? null
                : expressions.expression(reference);
        if (expression == null) return null;
        Term value = dispatch(expression, whole(expression, null), origin);
        sideCondition(value.precondition);
        return value;
    }

    /**
     * The sort a WHOLE value is asked at -- one a write stored, a read
     * joins or a row publishes: an object the VM named is the reference it
     * is, whatever its class; any other value the sort its reader expects.
     * An operator asks for its own operands, and a named container there
     * is its state, as its class's sort says.
     */
    static Sort whole(JsonElement value, Sort expected) {
        return named(value) && (expected == null
                || !expected.containerState()) ? Sort.REF : expected;
    }

    /**
     * One lowered expression: its text, its value (facts), what it reaches,
     * and why it is refused.  A refused construct inside it is a fresh name, so the
     * text still names what the rest reaches (the closure's question); only
     * an unrefused one may stand in a query ({@link #ok}).  A read bound by
     * its mint or its pin after its join refused is a constant in the text;
     * what that join did lower is still what the rest reaches
     * ({@link #reach}), and a query standing on that constant is refused as
     * the join would have refused it.
     */
    public static final class Lowered {
        private final String text;
        private final Term value;
        private final String refusal;
        /** The texts of the joins a mint or a pin stood in for. */
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

        /**
         * Whether it may stand in a query: nothing refused, and no mint or
         * pin standing in for a join that refused (a flip over that
         * constant is one its join would have dropped).
         */
        public boolean ok() {
            return refusal.isEmpty() && !text.isEmpty() && dropped.isEmpty();
        }

        /** The lowered text, a refused construct as its fresh name. */
        public String text() {
            return text;
        }

        /**
         * The value with its Java-level facts (a String's nullness, an
         * integral's width), in this session's names; null for a published
         * term ({@link #lowerTerm}) or a refusal.
         */
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

    // ------------------------------------------------------------------
    // Opening and closing one session's conjunction.
    // ------------------------------------------------------------------

    /**
     * Opens one conjunction in one session's scope, with the session's
     * expression table, against which {@link #statedTerm} resolves
     * references.  Identities and side conditions are per execution: one
     * constant for two sessions' objects makes satisfiable paths unsat.
     */
    /**
     * EVERY SESSION ON THE RECORDING'S TIMELINE.  A replay runs on its own
     * host's clock, started later than the recording (a plant is a skew off
     * that host, {@code runtime.NodeClocks}), so an instant it computed
     * outside every clock root -- a key's expiry from a startup reading --
     * is a constant on its own clock, while every clock cell is one symbol
     * on the recording's timeline.  {@code bases}: session -> clock symbol
     * -> how far that session's host read it later than the recording
     * ({@code Composer#clockBases}); a constant compared with a clock cell
     * in that session is that much earlier on the recording's timeline
     * ({@link #onTimeline}).  hdfs-11741 L1: dn1's first expiry check
     * compared each replay's own startup keys, 9 to 11 minutes late, with
     * the one dn1 clock.
     */
    void clockBases(Map<String, Map<String, Long>> bases) {
        clockBases = bases == null
                ? Collections.<String, Map<String, Long>>emptyMap() : bases;
    }

    public void begin(String sessionId, SessionJoin sessionJoin,
                      ExpressionTable expressions) {
        // NESTED, not replaced: an arm is lowered in its producer's scope
        // mid-path; overwriting the path's frame would leave the rest of the
        // path with no join, no table and no refusal sink.
        frames.push(new Frame(open, scope, join, openTable, memo, still,
                statedBases, arm));
        this.open = new Raised();
        raising.add(open);
        this.scope = sessionId;
        this.join = sessionJoin;
        this.openTable = expressions;
        this.memo = new HashMap<MemoKey, Attempt<?>>();
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

    /**
     * Closes it, answering the side conditions its lowering raised.  Its
     * refusals are the caller's to read before ({@link #openRefusals}); its
     * gaps reach the frame enclosing it, whatever the caller does with the
     * conjunction.
     */
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
        return new ArrayList<String>(closed.conditions);
    }

    /** One enclosing conjunction, kept while a nested one is open. */
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

    /**
     * What one frame raised: REFUSALS (the value does not stand), SIDE
     * CONDITIONS (what its lowering requires of it: definedness, recorded
     * readings, container requires) and GAPS (cuts, sort conflicts, pinned
     * returns, unanswered candidates).  Held until committed to the frame enclosing it.
     */
    private final class Raised {
        private final Set<String> refusals = new LinkedHashSet<String>();
        private final Set<String> conditions = new LinkedHashSet<String>();
        /** The texts of joins a mint or a pin stood in for ({@link
         *  Lowered#reach}). */
        private final Set<String> dropped = new LinkedHashSet<String>();
        private final Set<String> cuts = new LinkedHashSet<String>();
        /** name -> "<held> and <new>". */
        private final Map<String, String> sortConflicts =
                new LinkedHashMap<String, String>();
        /** method-return symbol -> the value its node states. */
        private final Map<String, String> pinnedReturns =
                new LinkedHashMap<String, String>();
        /** What could not be bound: FREE or HELD ({@link #unbound}). */
        private final List<Unbound> unbound = new ArrayList<Unbound>();
        /** A named DIAGNOSTIC that refuses nothing -> why
         *  ({@link #diagnostics}). */
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

        /** Everything another frame raised, as this frame's own. */
        private void all(Raised other) {
            for (String subject : other.refusals) refusal(subject);
            if (this != root) dropped.addAll(other.dropped);
            for (String predicate : other.conditions) condition(predicate);
            gaps(other);
        }

        private void gaps(Raised other) {
            cuts.addAll(other.cuts);
            sortConflicts.putAll(other.sortConflicts);
            pinnedReturns.putAll(other.pinnedReturns);
            unbound.addAll(other.unbound);
            diagnostics.putAll(other.diagnostics);
        }
    }

    /** The innermost frame, made on the first thing raised into it. */
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

    /** A node by identity (the decoder shares it), and the sort asked. */
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

    /**
     * One lowering and what it raised, held in a frame of its own until
     * {@link #commit}ted to the frame enclosing it; dropped, it raised
     * nothing.
     */
    private static final class Attempt<T> {
        private final T value;
        /** Null when it raised nothing. */
        private final Raised raised;

        private Attempt(T value, Raised raised) {
            this.value = value;
            this.raised = raised;
        }

        /** What it lowered to: a refused construct as its fresh name. */
        public T value() {
            return value;
        }

        /** Whether it lowered with no refusal. */
        public boolean lowered() {
            return raised == null || raised.refusals.isEmpty();
        }

        /** What it refused, each cause once. */
        private Set<String> refusals() {
            return raised == null ? Collections.<String>emptySet()
                    : raised.refusals;
        }
    }

    /** One lowering run in a frame of its own ({@link #raising}). */
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

    /** Keeps what an attempt raised, raised where it is committed. */
    private <T> T commit(Attempt<T> attempt) {
        if (attempt.raised != null) top().all(attempt.raised);
        return attempt.value;
    }

    /**
     * One node lowered once per conjunction ({@link #memo}), committed on
     * every hit: each lowering reaching it rests on what it raised.  A node
     * reached again while its own lowering is in progress ({@link
     * #lowering}) is its own input: the DAG has no cycle, so the lowering
     * came back to it through a value it asked by identity -- a candidate
     * object's field ({@link #fieldOf}) or a state a store published ({@link
     * #answerOf}) -- whose one write or state rests on the very node asking
     * (hdfs a40h2 FsDatasetImpl-1092/-1424: {@code b.numBytes =
     * f(owner.numBytes)} where the owner may be {@code b}, a recursion that
     * filled an 8 GB heap).  That value was read before it was written, so it
     * has no answer there: {@code cycle} refuses it by name ({@link
     * #LOWERING_CYCLE}), and the attempt asking it drops that candidate.
     */
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

    /** The refusal of a node reached inside its own lowering. */
    private static final String LOWERING_CYCLE = "LoweringCycle";

    private void cycle(String origin) {
        refuse(LOWERING_CYCLE + ":" + origin, "this value was reached again "
                + "inside its own lowering, through a candidate's field or "
                + "a state asked by identity whose write rests on it: it was "
                + "read before that write, which therefore answers nothing "
                + "here");
    }

    /**
     * The conjunction now open is the body of {@code selector}'s arm, and
     * so is every one nested in it until it ends: each value it leaves
     * unbound names that arm ({@link Unbound#arm}).
     */
    public void arm(String selector) {
        arm = selector;
    }

    /** How many values the innermost frame left unbound so far, for
     *  {@link #unboundRollback}. */
    public int unboundMark() {
        return top().unbound.size();
    }

    /** Takes back the values left unbound since {@code mark}: an arm
     *  refused, or a copy of one taken already, states none. */
    public void unboundRollback(int mark) {
        List<Unbound> held = top().unbound;
        held.subList(Math.min(mark, held.size()), held.size()).clear();
    }

    /** What the conjunction now open refused, each cause once. */
    public List<String> openRefusals() {
        return open == null ? Collections.<String>emptyList()
                : new ArrayList<String>(open.refusals);
    }

    // ------------------------------------------------------------------
    // Results and their definedness.
    // ------------------------------------------------------------------

    /** A named refusal, as a fresh value of the refused construct's sort. */
    private Term refuse(Reason reason, String origin, String detail,
                        Sort sort) {
        refuse(reason.composedSubject(origin, detail), "");
        return free(sort, IntegralWidth.NONE);
    }

    /** The result, defined only where every input is. */
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

    /** One lowered value with no definedness obligation of its own. */
    private static Term result(String text, Sort sort, Term... inputs) {
        return definedResult(text, sort, IntegralWidth.NONE, "true", inputs);
    }

    private static Term result(String text, Sort sort, IntegralWidth width,
                               Term... inputs) {
        return definedResult(text, sort, width, "true", inputs);
    }

    /** Java's {@code &&}/{@code ||}: the right operand is evaluated only
     *  where the left does not decide. */
    private static Term shortCircuit(String text, Term left, Term right,
                                     boolean conjunction) {
        String rightEvaluated = conjunction ? left.text
                : "(not " + left.text + ")";
        return Term.of(text, Sort.BOOL).withPrecondition(
                and(Arrays.asList(left.precondition,
                        "(=> " + rightEvaluated + " " + right.precondition
                                + ")")));
    }

    /**
     * Where a String operation is defined: each dereferenced operand is a
     * non-null String, and every operand evaluated.  Operands of unknown
     * nullness are refused before ({@link #nullnessUnknown}).
     */
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

    /**
     * Whether an operation dereferences a String whose nullness nothing
     * stated (a container codec's value): its definedness cannot be said,
     * so it is refused, as {@code == null} and {@code equals} are.  Taken as
     * null, it asserted {@code (not true)} into every query on SOLR-18413's
     * update path and made each flip UNSAT.
     */
    private static boolean nullnessUnknown(List<Term> dereferenced) {
        for (Term value : dereferenced) {
            if (value.sort == Sort.STRING && value.stringNullness.isEmpty()) {
                return true;
            }
        }
        return false;
    }

    /** One integral term's Java domain, asserted once per term. */
    private void assertJavaIntegralDomain(String term, String javaType) {
        JavaPrimitiveSmtSemantics.IntegralDomain domain =
                JavaPrimitiveSmtSemantics.domainOfJavaType(javaType);
        if (term.isEmpty() || domain == null || !integralDomains.add(term)) {
            return;
        }
        assertPlain(VmTermLowering.integralRange(domain.lower, term,
                domain.upper));
    }

    /**
     * What a joined read observed, conjoined into the open conjunction
     * (never asserted globally: other paths' arms may give the expression
     * other values).
     */
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

    // ------------------------------------------------------------------
    // Leaves.
    // ------------------------------------------------------------------

    private Term symbolTerm(JsonObject expression, Sort expected) {
        String raw = primitiveString(expression, "_exp");
        // "N" is Java null (VmExpressionIr.SYMBOLIC_NULL), not a name: as
        // an opaque identity "x != null" would say nothing about nullness.
        if (VmExpressionIr.SYMBOLIC_NULL.equals(raw)) {
            return nullLeaf(expected);
        }
        if (VmExpressionIr.SYMBOLIC_VOID.equals(raw)) {
            return Term.of("true", Sort.BOOL);
        }
        String javaType = primitiveString(expression, "_java_type");
        // An object the VM named, asked as a reference, is its identity
        // whatever its class ({@link #whole}).
        Sort sort = expected == Sort.REF
                && (VmRows.referencedObjectRid(raw) > 0L
                || VmRows.placedObject(raw))
                ? Sort.REF : leafSort(javaType, expected);
        if (sort == null) sort = Sort.REF;
        Declared held = declarations.get(raw);
        if (held != null && held.stated) {
            // The stated declaration wins over the node's shape: one
            // variable, one sort.
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

    /** A MethodReturnSymbolExp's name (methodSymbolizer.cpp). */
    private static final Pattern METHOD_RETURN =
            Pattern.compile("M_[A-Z]_return[0-9]+");
    /**
     * The member a method-return node states its CALL in (VM f14):
     * {@code holder} and {@code name} of the callee, its {@code descriptor},
     * and its argument expressions as {@code arguments}.
     */
    private static final String CALL = "call";

    /**
     * The result of a library call the VM does not model (a
     * MethodReturnSymbolExp, {@code M_<t>_return<n>}): no row declares it,
     * and what it is rests on the call its node states ({@link #CALL}).  A
     * callee this lowering knows is its RELATION over the lowered arguments
     * ({@link #knownCall}), whatever they rest on.  Any other whose
     * arguments rest on what can move ({@link #movers}) is FREE, named with
     * them ({@link #unbound}): a pin would hold a root moved through the
     * call as a constant.  Over nothing that moves it is PINNED to the value
     * the node states it returned, by an assertion named for an unsat core
     * to show the reliance ({@link #pinnedReturns}).
     * A node stating no call (a VM before f14) is refused, since what its
     * value was computed from is not known.  The pinned name is this
     * session's, so two runs' results of one symbol are two values.
     */
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
            // A flip query reads the lowering's facts, a composition its
            // named assertions.
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

    /**
     * THE PIN of a container query its chain cannot decide (no stated base
     * under it, {@link ContainerSmtCodec#term}), as a method return's
     * ({@link #methodReturn}): the answer its call stated it returned
     * ({@code concreteValue}) -- a member of an opaque root, a presence a
     * muted body tested -- named for the query's {@code answer} id and
     * pinned by an assertion named for an unsat core, where nothing it rests
     * on can move ({@link #moves}: its keys, positions, owner and chain).
     * Null otherwise, and the relation stands, free over its opaque base:
     * a pin there would cut the witnesses that move it.  Named, never
     * silent: one DIAGNOSTIC per query kind and session.
     */
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

    /**
     * The MINT of a cell no run stated ({@code UNKNOWN}): what a callback
     * the run never ran would have stored -- a free {@code Value} named
     * {@code unknown__} for its session and id, so the arm the run did not
     * take holds any value there.  Named, never silent: one DIAGNOSTIC per
     * session.
     */
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

    /**
     * The relation of a call this lowering knows, over its lowered
     * arguments, or null when it knows none.  {@code Integer.parseInt} and
     * {@code Long.parseLong} of a String (radix 10) are its decimal reading
     * with Java's sign and range, defined as the JVM that returned it: an
     * optional sign and one or more digits within the type's range.  A
     * digit outside ASCII, which Java reads too, is outside what z3's
     * {@code str.to_int} states, so such a string has no value here.
     * {@code String.valueOf} and {@code Integer}/{@code Long.toString} of an
     * integral are the inverse, its decimal rendering, and a parse of a lone
     * decimal rendering is the value rendered, widened to the parse's type
     * ({@link StringIdentities#parsedOperand}).  A known callee whose
     * arguments this lowering cannot state is refused by name.
     * {@code callee} is {@code "<holder> <name>"}, as a method-return node's
     * call and a {@code MethodExpression} spell it.
     */
    private Term knownCall(String callee, JsonArray arguments,
                           String origin) {
        if (RENDERINGS.contains(callee) && arguments.size() == 1) {
            return javaToString(arguments, origin);
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
            // The rendering's own lowering lowers it first, so falling
            // through below raises nothing it would not have.
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

    /** The callees that render an integral as its decimal String. */
    private static final Set<String> RENDERINGS = new LinkedHashSet<String>(
            Arrays.asList("java/lang/String valueOf",
                    "java/lang/Integer toString", "java/lang/Long toString"));

    /**
     * Java null at the expected sort: {@code nullRef}, or the null cell for
     * a boxed VALUE.  A container STATE cannot be null, so null compared
     * against one is refused by name.
     */
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

    private Term placeholderTerm(JsonObject expression) {
        String function = primitiveString(expression, "_place_holder_func");
        int count = optionalInteger(expression, "_count", -1);
        if (!"currentTimeMills".equals(function) || count < 1) {
            refuse("PlaceholderExpression:"
                    + (function.isEmpty() ? "unknown" : function)
                    + "#" + count, "");
            return leaf(Sort.INT, primitiveString(expression, "_java_type"));
        }
        String name = symbols.mint("environment__",
                scope + SEPARATOR + function + "#" + count, 10);
        declare(name, Sort.INT);
        assertJavaIntegralDomain(name, "J");
        return Term.of(name, Sort.INT, IntegralWidth.JAVA_LONG);
    }

    /**
     * How one read is bound, by level: a guarded read node
     * ({@link #guardedReadTerm}) or a read row ({@code Composer#stateJoins}).
     * The rule and its order are {@link #bind}'s alone.
     */
    interface Binder<T> {
        /** The joined value: the write, or the read's own projection. */
        Term join(JsonElement value);

        /** JOIN: the value lowered with no refusal. */
        T joined(Term value);

        /** MINT: the placeholder that created the version. */
        T minted(String symbol);

        /** PIN: what the recording states the read returned, else null. */
        T pinned();

        /** What the recording states the read returned, as its row or
         *  node spells it ("" for none): what a pin holds, named. */
        String returned();

        /** FREE: the read unconstrained, since what it rests on can move
         *  and a pin would hold it while a witness moves that. */
        T free();

        /** FREE, its writer a frame whose producer moves ({@link
         *  RefusalFrame}): as {@link #free}, a leaf no plant reaches. */
        default T framed() {
            return free();
        }

        /**
         * REFUSE, by name.  {@code joined} is the refused join's value (its
         * refused constructs fresh names), already committed, or null.
         */
        T refused(Term joined, String subject, String detail);
    }

    /**
     * THE ONE BINDING RULE, for a read of one location at one version, at
     * every level that binds one: JOIN, the write it observed (or the
     * read's own projection of it), if that lowers with no refusal; else
     * MINT, the placeholder that created the version (a mint is not a
     * write); else PIN, what the recording states it returned; else
     * REFUSE.  Never enumerate retained versions for the solver to pick
     * from.
     *
     * <p>A join that refused gives way to the mint; else, where what the
     * refused write rests on can move ({@link #movers}: a root, a clock, a
     * handoff or a read a family re-pairs), the read is FREE -- a pin would
     * hold the run's value while a witness moves what it rests on (C1
     * review H1: {@code parseInt(valueOf(R))}), losing the witnesses that
     * move it; free, it over-approximates and CONFIRM filters -- named with
     * what it rests on ({@link #unbound}); else, resting on nothing that
     * moves, the PIN.  Dropped, the join raised nothing.  A write its
     * occurrence made on an arrival it refused (a {@link RefusalFrame})
     * was computed on that arrival as a constant: where the producer the
     * refused attach's handle names rests on what can move, the read is
     * FREE over it, as any value whose stated producer moves.  A PIN of a
     * version no write row states holds a value whose producer no row
     * states: HELD, named ({@link #unbound}), never silent.</p>
     *
     * <p>{@code projected} is the node's own {@code observedVersion}
     * expression, the projection the read performed (e.g.
     * {@code SIZE(state)}): used only once a write row has stated the
     * version.  Consulted without one, it binds the read to a value no row
     * stands behind.</p>
     */
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

    /** Records a value left free over what it rests on ({@link
     *  #unbound}). */
    private void freed(String subject, String why, Set<String> movesWith) {
        top().unbound.add(new Unbound(Unbound.FREE, subject, "", why,
                new ArrayList<String>(movesWith), arm));
    }

    /**
     * One read row's binding ({@link #bind}), whose side conditions are the
     * binding's own: when {@code binding} answers that it bound the read,
     * what its lowering required (container membership, cell tags, recorded
     * readings) is answered here, to be stated WITH the binding and raised
     * nowhere else; otherwise it is raised as any lowering's.  Everything
     * else it raised is raised as usual.  A state join the conjunction never
     * asks about ({@code Composer#statedJoins}) then takes its requires with
     * it, instead of leaving them on symbols nothing else names
     * (hdfs-17899-bug3 r4: a byte array's membership and cell tag at a free
     * index, per unasked join of a decoded length).
     */
    public List<String> ownConditions(Supplier<Boolean> binding) {
        Attempt<Boolean> held = attempting(binding);
        List<String> own = new ArrayList<String>();
        if (held.raised != null && Boolean.TRUE.equals(held.value)) {
            own.addAll(held.raised.conditions);
            held.raised.conditions.clear();
        }
        commit(held);
        return own;
    }

    /**
     * THE ONE PREDICATE every pin asks -- a refused join's ({@link #bind}),
     * a method return's ({@link #methodReturn}), a container answer's
     * ({@link #answered}), in a composition and in a flip query alike:
     * whether anything this expression rests on can move in a witness.  A
     * leaf naming a symbol the open join says {@link SessionJoin#moves}, or
     * a read the stage may {@link SessionJoin#repaired re-pair} (a
     * composition's, the anchor's reads its STATE families re-pair; a flip
     * query's, every read of a location with write rows), of a version a
     * moving mint made, or of a write that rests on one.  Each node once per
     * conjunction; the nodes of a walk that found nothing are not walked
     * again ({@link #still}).
     */
    private boolean moves(JsonElement expression) {
        return !movers(expression, false).isEmpty();
    }

    /**
     * What this expression rests on that can move ({@link #moves}): each
     * moving symbol, re-paired read and moving mint, all of them, or (not
     * {@code all}) the first found.
     */
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
                long version = observedVersion(object);
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

    /**
     * A read node, by {@link #bind}.  Joined, it is the symbol its row
     * joined, so a STATE family that binds the symbol moves it; else the
     * value, never a pinned symbol (the projection that lowered is what the
     * read returned).  Refused, the MINT; then the symbol its row was
     * pinned to; then the value the node states it returned.
     */
    private Term guardedReadTerm(JsonObject expression, Sort expected,
                                 String origin) {
        JsonObject location = JsonFields.object(expression, "location");
        String key = locationKey(location);
        long version = observedVersion(expression);
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

    /**
     * A container query a STATE family may re-pair ({@link
     * SessionJoin#repaired}: the anchor's read of the container), asked of
     * the state the family chooses -- the read's own symbol, stated at the
     * container's sort by its join and bound by each writer arm
     * ({@code ComposedFamilies#stateFamilies}) -- not of the run's chain:
     * inlined, the chain is what the run read, which no family moves
     * (zk-bugs-election-offer: the getData's lookup of an offer in
     * ZooKeeper's node map, folded to the run's DataNode).  Its chain, for
     * what a query requires of one (a base the VM walked), is the observed
     * version's ({@link #MOVED_CHAIN}): every version of one location
     * descends from that base.  A view's positions are its chain's, so a
     * query through a view, like any other read's, is the run's.
     */
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

    /** The member a moved read's state symbol carries its observed chain
     *  in ({@link #movedQuery}, the host's {@code chain}). */
    private static final String MOVED_CHAIN = "inSessionObservedChain";

    /**
     * The one symbol this session's rows JOINED a scalar read of this
     * version to, at the joined value's sort.  The read is that symbol, not
     * the written value inlined: the join the conjunction then asks about
     * binds it to the same value, and at the anchor a STATE family binds it
     * to the writer it chooses instead -- inlined, no family could move it
     * (commit-gs.TestFileAppend2-testSimpleAppend v71: two families, phi on
     * constants).  Never a PINNED symbol: a projection that lowered is what
     * the read returned, and the pin a constant beside it (C1 review H2).
     * A container read keeps its projection.
     */
    private String rowSymbol(String key, long version, Sort sort) {
        if (sort.containerState()) return null;
        Set<String> named = join.readSymbols(key, version);
        if (named.size() != 1) return null;
        String read = named.iterator().next();
        Declared held = declarations.get(read);
        return held != null && held.stated && held.sort == sort
                && !pins.contains(scope + SEPARATOR + read) ? read : null;
    }

    /** The one symbol of a read of this version {@link #pin}ned here. */
    private String pinnedSymbol(String key, long version) {
        Set<String> named = join.readSymbols(key, version);
        if (named.size() != 1) return null;
        String read = named.iterator().next();
        return pins.contains(scope + SEPARATOR + read) ? read : null;
    }

    /**
     * Declares one read's symbol, bound by {@code Composer#pin} to what its
     * row states it returned: a read of its version in this session that
     * does not join lowers to it ({@link #guardedReadTerm}).
     */
    public void pin(String symbol, Sort sort) {
        declareStated(symbol, sort);
        if (pins.add(scope + SEPARATOR + symbol)) {
            // A read of its version lowers to it from now on
            // ({@link #pinnedSymbol}), and a memoized one did not.
            memo = new HashMap<MemoKey, Attempt<?>>();
        }
    }

    /**
     * A path is composed from here on: no read is movable until it says so,
     * and no nested selector is minted yet.  A read another path made
     * movable is its own session's; lowered in this path (a message arm in
     * the sender's session) it is the run's pairing, since a query through
     * it would mint selectors no arm of this path binds.
     */
    public void path() {
        movable.clear();
        nestedSelectors.clear();
        memo = new HashMap<MemoKey, Attempt<?>>();
    }

    /**
     * Declares one read of the path being composed a STATE family may bind
     * to another writer's value ({@code ComposedFamilies#stateFamilies}): a
     * field projected through it is then the field of the object it is
     * ({@link #projection}).  That read alone: another read of its location
     * and version (a writer's own lookup) keeps the run's object.
     */
    public void movable(ReadRow read) {
        if (movable.add(scope + SEPARATOR + readKey(
                locationKey(read.location()), read.seq()))) {
            memo = new HashMap<MemoKey, Attempt<?>>();
        }
    }

    /**
     * One recorded symbol as the leaf the VM would have serialized, so a
     * row's symbol goes through the one leaf rule of {@link #symbolTerm}.
     */
    private static JsonObject symbolNode(String symbol, String javaType) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "SymbolExpression");
        node.addProperty("_exp", symbol);
        node.addProperty("_java_type", javaType == null ? "" : javaType);
        return node;
    }

    /**
     * The term one row states as the value its read returned, or null (the
     * caller names the refusal).  The one reading of a recorded value, for
     * pins and {@code concreteValue} alike, spelled as
     * {@link ReadRow#returned} spells it: a String is its content, a
     * reference or {@code "N"} goes through {@link #symbolTerm}, and a
     * scalar is its literal at the row's Java type.
     */
    Term statedValue(String concreteValue, String javaType) {
        String text = concreteValue == null ? "" : concreteValue.trim();
        if (text.isEmpty()) return null;
        // A String literal is a String whatever the row's Java type says.
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

    /**
     * The CELL a one-element read observed, when the join handed back the
     * whole container: {@code indexed_read(state, slot)} with the location's
     * own slot.  Returning the state instead leaks it into scalar operators.
     *
     * <p>An associative location names its key only by hash, so that case
     * is refused by name.</p>
     */
    private Term element(Term value, JsonObject expression,
                         JsonObject location, String key, long version,
                         Sort expected) {
        if (!value.sort.containerState()) return value;
        String javaType = primitiveString(expression, "_java_type");
        Sort cell = JavaSmtSorts.sortOfJava(javaType);
        // The read IS of the container: the value is what it read.
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
            // The codec named WHY; this names WHICH node (a field has no
            // operation, so fall back to owner@offset or shape).
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

    /** A codec value as a term: a String keeps the nullness its cell
     *  states, else it stays unknown. */
    private static Term lowered(ContainerSmtCodec.Term value) {
        Sort sort = VmTermLowering.sortOfContainer(value.sort);
        return value.nullness.isEmpty()
                ? Term.vm(value.text, sort, value.integralWidth)
                : Term.of(value.text, sort, value.integralWidth,
                value.nullness, "", "true");
    }

    // ------------------------------------------------------------------
    // What is asked through an owner a family may re-point.
    // ------------------------------------------------------------------

    /** A candidate object with no answer ({@link #fieldOf}). */
    private static final String CANDIDATE_UNANSWERED = "CANDIDATE_UNANSWERED";

    /**
     * THE MOVE of a field projection ({@link ContainerSmtCodec#field}).  Its
     * pair states the run's own object and what that object's field held.
     * Through an owner read a STATE family may re-point ({@link #movable}),
     * the owner may be another writer's object, and {@code owner.f} is the
     * field of the object it is ({@link #perCandidate}): the run's cell for
     * the run's object, each other candidate's as its rows state it
     * ({@link #fieldOf}).  The run's cell under every arm read one object's
     * field under another's pairing (SOLR-18406: latestCommit's four
     * writers, phi on cell 1182#24 whichever one z3 chose).  Through any
     * other owner the projection is the run's cell, and rests on neither the
     * owner's read chain nor its refusals.
     */
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

    /** The member a node names the reference it was reached through by. */
    private static final String OWNER = "owner";
    /** What a node states it returned ({@link ReadRow#returned}). */
    private static final String CONCRETE_VALUE = "concreteValue";

    /**
     * The row of the read a node's {@code owner} is, when a STATE family may
     * re-point it ({@link #movable}), else null: then what is asked through
     * it is asked of the run's own object.
     */
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

    /**
     * THE ANSWER PER CANDIDATE IDENTITY, the one rule for what is asked
     * through an owner a family may re-point (a field here, a container
     * query in R3-REFCONT §1.1): {@code (ite (= owner id_1) a_1 ... a_n)},
     * the first case the run's own object, defined only where the owner is
     * one of the candidates and that case's answer is defined.  An object
     * with no answer is no case, so a pairing that delivers it holds by no
     * free value: fail closed.  Identities of one session are distinct
     * ({@link #assertIdentitiesDistinct}), so the order decides nothing.
     */
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

    /**
     * {@link #perCandidate} as a codec term of {@code run}'s sort; a String
     * answer is null where its case's is, by the same test of the owner,
     * and of unknown nullness where any case states none.
     */
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

    /**
     * A lowered value as the codec takes it, with its Java width (shift and
     * bitwise operators are typed: ISHR is not LSHR) and a String's
     * nullness as its lowering stated it: a recorded String is not null,
     * and a value the lowering knows is not left unknown at the codec.
     */
    private static ContainerSmtCodec.Term codecTerm(Term value) {
        return value.sort == Sort.STRING
                ? ContainerSmtCodec.Term.string(value.text,
                value.stringNullness)
                : new ContainerSmtCodec.Term(value.text,
                VmTermLowering.containerSortOf(value.sort),
                value.integralWidth);
    }

    /**
     * The run's own object at one projection, as the VM spells an object:
     * the owner of the cell {@code concreteValue} read, else
     * {@code concreteOwner} when it names an object; null when the pair
     * names neither (a reference expression is not an identity).
     */
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

    /**
     * One object a re-pointable owner may be: its identity as the VM spells
     * it, the seq of the first write of the owner's location that reaches
     * it, and the writes that stored this very object, none when only a
     * read inside a write reaches it ({@link #candidates}).
     */
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

    /**
     * C(r) of a read of one location (R3-REFCONT §1.3): the objects this
     * session's writes of the location reach, of one class or ({@code
     * null}) any, by rid, with the first write reaching each.  A write
     * reaches what its expression names and, through each read in it, what
     * the write that read observed names: a superset of what it stored, so
     * no first store is later than the true one.  Walked in seq order over
     * one walked set, a node is credited to the first write reaching it.
     */
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
                                    observedVersion(node));
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

    /** Whether a node is an object the VM named ({@code M_L'<class>'_<rid>}). */
    static boolean named(JsonElement node) {
        return VmExpressionIr.SYMBOL_TYPE.equals(VmExpressionIr.typeOf(node))
                && VmRows.referencedObjectRid(primitiveString(
                node.getAsJsonObject(), "_exp")) > 0L;
    }

    /**
     * One candidate's field as its rows state it, a value the object held
     * whenever the owner could be it: the one write of that cell in this
     * session, made before the owner's location first stored the object;
     * or, never written, the one value every read of it states at one
     * version.  Any other cell has no one value an arm delivering the
     * object reads: null, and named ({@link #diagnostics}).
     */
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

    /**
     * The one value every read of a cell no write of this session touched
     * states, all at one version, or null ({@link #statedValue}).
     */
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

    /** A candidate whose container state no row states ({@link #answerOf}). */
    private static final String REFERENT_STATE_UNSTATED =
            "REFERENT_STATE_UNSTATED";
    /** The relations that walk their receiver's state without changing it:
     *  a query through one asks the state beneath. */
    private static final Set<String> VIEWS = new LinkedHashSet<String>(
            Arrays.asList("ITERATOR", "KEY_VIEW", "VALUE_VIEW", "ENTRY_VIEW",
                    "NEXT", "ENTRY"));

    /**
     * THE MOVE of a container query (R3-REFCONT §1.1), a query's answer as
     * {@link #projection} is a field's.  The relation answers over the
     * state of the object its owner read returned.  Through an owner a STATE
     * family may re-point ({@link #movable}) it is asked of the object the
     * owner is ({@link #perCandidate}): for each object a store of the
     * owner's location stored, the same relation over each state of it the
     * reader could have seen through that store ({@link #answerOf}), and
     * the run's answer where the object is the run's and the store the one
     * the read observed.  Through any other owner the answer is the run's.
     * The reads this query answers are the ones asked through the owner
     * ({@link #askedThrough}): what CONFIRM holds a chosen state to.
     */
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

    /**
     * The object a reference read returned: the identity the write it
     * observed stored, else the one its row states; null when neither
     * names an object.
     */
    private JsonObject identityRead(String key, ReadRow read) {
        JsonElement written = join.writeExpression(key,
                read.observedVersion());
        if (named(written)) return written.getAsJsonObject();
        return VmRows.referencedObjectRid(read.concreteValue()) > 0L
                ? symbolNode(read.concreteValue(), read.javaType()) : null;
    }

    /**
     * One object's answer: the relation over each state of it the reader
     * could have seen through a store of it ({@link #statesOf}), each chosen
     * by a nested selector {@code nest__}, one per (read, object, version),
     * so every query through the read sees the object at one version; an
     * arm delivering a store holds them to the states seen through that
     * store ({@link #storeChoice}).  The run's own object ({@code run}, its
     * answer as the run saw it) answers so through the store the read
     * observed, and through any other store of it -- a re-store publishes
     * a later state -- each state seen from that store's own referent on;
     * there the selectors pick at most one, none being the run's answer.
     * An answer holds only where the owner is this object, so what its
     * lowering requires is its own precondition, never the path's; a state
     * that does not lower is no option.  A store that states no container
     * state is no case, so the pairings delivering the object through it are
     * refused, and named.
     */
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
        // The last option (the run's answer, for the run's object) stands
        // where no other is chosen; each other holds only under its
        // selector, and a state this query has no answer at is no option.
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

    /** At most one of these selectors. */
    private static String atMostOne(List<String> selectors) {
        if (selectors.size() < 2) return "true";
        StringBuilder sum = new StringBuilder("(<= (+");
        for (String selector : selectors) {
            sum.append(" (ite ").append(selector).append(" 1 0)");
        }
        return sum.append(") 1)").toString();
    }

    /** The nested selector of one (read, object, version), declared. */
    private String nested(ReadRow read, String object, long version) {
        String selector = symbols.mint("nest__", scope + SEPARATOR
                + read.symbol() + SEPARATOR + object + SEPARATOR + version,
                12);
        declare(selector, Sort.BOOL);
        nestedSelectors.add(selector);
        return selector;
    }

    /**
     * Records the reads the query now lowered answers, as asked through
     * {@code owner}: the rows of the container read whose value is being
     * lowered ({@link #answering}) that the owner's reader made.  None when
     * the query is lowered outside every read of a container.
     */
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

    /**
     * What a STATE family's arm delivering one store to a read holds the
     * nested selectors of the stored object to: one of the states the reader
     * could have seen through that store, ({@code false}) none, or
     * {@code ""} when no query through the read asked it or the store is
     * the one the read observed of the run's own object, whose answer is
     * the run's.
     */
    public String storeChoice(String symbol, WriteRow store) {
        Map<String, WriteRow> through = storeStates.get(scope + SEPARATOR
                + symbol + SEPARATOR + store.version());
        return through == null ? ""
                : VmTermLowering.or(new ArrayList<String>(through.keySet()));
    }

    /**
     * The states of the object one store delivers to one read of one
     * session that a query through the read may be answered from
     * ({@link #storeChoice}), each with its nested selector and the reads
     * the queries answered: what CONFIRM holds a witness that chose that
     * store and selector to.  None for the store the read observed of the
     * run's own object: its queries keep what the run read.
     */
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

    /** Every nested selector the path being composed minted, in any scope
     *  ({@link #path}): each one its families must bind. */
    public Set<String> nestedSelectors() {
        return Collections.unmodifiableSet(nestedSelectors);
    }

    /**
     * One state a query through a re-pointable read may have seen: its
     * nested selector, the write of that version of the stored object's
     * container, and the reads the query answered (none when it was asked
     * outside every read of the container, which CONFIRM cannot hold).
     */
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

    /** One read of one location at one version ({@link #answering}). */
    private static final class ReadAt {
        private final String key;
        private final long version;

        private ReadAt(String key, long version) {
            this.key = key;
            this.version = version;
        }
    }

    /**
     * The versions of a stored container a reader could have seen
     * (R3-REFCONT §1.4), of its {@code writes}: of those from the one the
     * store saw on, the one live at the read in this session's order (the
     * store's own when every one came later), and each later one whose
     * writer may have run before the reader in another schedule
     * ({@code concurrent}); none written after the read on its own thread
     * or request.  The floor is the delivering store's own referent, so a
     * re-store shows only what it published on.  ONE rule: COMPOSE answers
     * from these states, and EXPLORE demands their writers
     * ({@code Corpus#referentStates}).
     */
    public static List<WriteRow> statesOf(
            List<WriteRow> writes, WriteRow.Referent state, ReadRow read,
            BiPredicate<OccurrenceAddress, OccurrenceAddress> concurrent) {
        List<WriteRow> versions = new ArrayList<WriteRow>();
        for (WriteRow version : writes) {
            if (version.version() >= state.version()) versions.add(version);
        }
        versions.sort(Comparator.comparingLong(WriteRow::seq));
        if (versions.isEmpty()
                || versions.get(0).version() != state.version()) {
            return Collections.<WriteRow>emptyList();
        }
        int live = 0;
        while (live + 1 < versions.size()
                && versions.get(live + 1).seq() < read.seq()) {
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

    /**
     * The relation asked of another state: its receiver, beneath the views
     * and iterators that walk it, is that state's chain, as the run's own
     * receiver is its object's; no copy names the owner, so none of them is
     * asked again, and none states the answer the run's object gave
     * ({@code concreteValue}, {@code answer}): that answer is that object's
     * alone, and pinned on another it would be every candidate's.
     */
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

    /**
     * An attempt's value, what its lowering required conjoined as its own
     * precondition instead of the open frame's; its gaps are kept.
     */
    private Term conditioned(Attempt<ContainerSmtCodec.Term> asked) {
        List<String> required = new ArrayList<String>();
        if (asked.raised != null) {
            required.addAll(asked.raised.conditions);
            top().gaps(asked.raised);
        }
        return lowered(asked.value()).withPrecondition(and(required));
    }

    /**
     * Each DIAGNOSTIC this lowering names without refusing what it lowered,
     * by subject, with why: a candidate object with no answer ({@link
     * #fieldOf}, {@link #answerOf}: the pairings delivering it are not
     * composed), a view whose positions are a bijection in no order
     * ({@code ContainerSmtCodec#requireAssociativeViewBijection}).
     */
    public Map<String, String> diagnostics() {
        return Collections.unmodifiableMap(root.diagnostics);
    }

    // ------------------------------------------------------------------
    // Identities.
    // ------------------------------------------------------------------

    /**
     * One execution-local identity, opaque but not free: an object the VM
     * named (a rid) is non-null and distinct from other rids of its session,
     * and one it placed unnamed ({@link VmRows#placedObject}) is non-null,
     * all recorded facts.  Left unsaid, a model can null a reference or merge
     * two keys (ZK7: the stat node a DataTree lookup returned, placed
     * unnamed, made the recording's own path reach the NoNode throw).
     */
    private String opaque(String raw, Sort sort) {
        // As a reference, an array is one object at every version its
        // spelling states (A<type>_<rid>-<version>); as a state it is not.
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

    /** "Different rids, different objects", once per session. */
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

    // ------------------------------------------------------------------
    // Containers.
    // ------------------------------------------------------------------

    /** The memo's sort for a container operand, whatever was expected. */
    private static final Object CONTAINER_OPERAND = new Object();

    private ContainerSmtCodec.Host host(final String origin) {
        return new ContainerSmtCodec.Host() {
            @Override
            public ContainerSmtCodec.Term state(
                    JsonElement identity, ContainerSmtCodec.Sort shape) {
                Sort stateSort = shape == ContainerSmtCodec.Sort.INDEXED
                        ? Sort.ARRAY_VALUE : Sort.MAP;
                // An object the VM named is its own state's root; any other
                // receiver is the reference it lowers to, whose state
                // assoc_state_of names.
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
                // A refused operand is null to the codec.
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
                // A cell holds what Java stores in it: an object, a
                // container included, is its reference.
                Term value = dispatch(expression, JavaSmtSorts.sortOfJava(
                        javaType).containerState() ? Sort.REF : null,
                        origin + ":container-value");
                String boxed = boxed(value, javaType);
                if (boxed.isEmpty()) {
                    // Name both the declared type and the lowered shape.
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
                return name(ContainerStateModel.unboxValue(value, javaType,
                        VmTermLowering.unboxedCellSort(
                                JavaSmtSorts.sortOfJava(javaType)), this));
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
                        read, "location")), observedVersion(read));
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

    /**
     * One cell's {@code Value}: the constructor its Java type names, else
     * the width its lowering carries -- an arithmetic node states no Java
     * type, and a long sum stored in a map is a Long cell that a
     * {@code getOrDefault(k, 0L)} reads back as {@code VLong} (SOLR-18406's
     * reservation, {@code nanoTime() + reserve}, was boxed {@code VInt} and
     * every read of it contradicted its own tag) -- else its sort.
     */
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

    /** One container subterm, lowered once and referenced by name. */
    private static final class SharedTerm {
        private final String name;
        private final Sort sort;
        private final String body;

        private SharedTerm(String name, Sort sort, String body) {
            this.name = name;
            this.sort = sort;
            this.body = body;
        }
    }

    /**
     * Names a pure container subterm (one define-fun), or returns it
     * unchanged; inlining the mutation chain at every read blows up the
     * formula.
     */
    private ContainerSmtCodec.Term name(ContainerSmtCodec.Term value) {
        if (value == null || value.text.isEmpty()
                || value.text.charAt(0) != '(') {
            return value;
        }
        Sort sort = VmTermLowering.sortOfContainer(value.sort);
        if (sort == Sort.UNKNOWN) return value;
        // Digest the SCOPED text: recorded symbols are per session, so two
        // sessions share a name only for the same closed term.
        String identity = sort.name() + SEPARATOR + scoped(value.text);
        String digest = ArtifactIO.digest(identity, 0);
        SharedTerm held = sharedTerms.get(digest);
        if (held == null) {
            held = new SharedTerm(symbols.mint("container_dag__", identity,
                    24), sort, value.text);
            sharedTerms.put(digest, held);
            sharedByName.put(held.name, held);
        }
        return value.nullness.isEmpty() ? new ContainerSmtCodec.Term(
                held.name, value.sort, value.integralWidth, value.indexedSize)
                : ContainerSmtCodec.Term.string(held.name, value.nullness);
    }

    // ------------------------------------------------------------------
    // The query.
    // ------------------------------------------------------------------

    /**
     * The text with every recorded symbol qualified by this session; for
     * the digest only, never emitted.
     */
    private String scoped(String text) {
        if (text == null || text.isEmpty() || scope.isEmpty()) return text;
        return SmtNames.substitute(text, token -> usedSymbols.contains(token)
                ? scope + SEPARATOR + token : null);
    }

    /**
     * Declares one name THIS LOWERING minted; a second, different sort is
     * a defect.
     */
    public void declare(String name, Sort sort) {
        put(name, sort, false);
    }

    /**
     * Declares one name a row of the recording states; a leaf naming it then
     * lowers to it instead of being cut.
     */
    public void declareStated(String name, Sort sort) {
        put(name, sort, true);
    }

    /**
     * States one name the recording gives a meaning to, as a corpus's own
     * are ({@link #SmtLowering(Map)}): a read of it lowers to it from now on
     * ({@link #rowSymbol}), and it joins the query only once the formula
     * names it.  A name already stated, or declared at another sort, stands.
     */
    public void state(String name, Sort sort) {
        Declared held = declarations.get(name);
        if (held != null && (held.stated || held.sort != sort)) return;
        declarations.put(name, new Declared(sort, true,
                held != null && held.inQuery));
        memo = new HashMap<MemoKey, Attempt<?>>();
    }

    /**
     * Puts a name the recording already states into the query, answering
     * whether it is stated; for callers holding text rather than leaves.
     */
    public boolean declareStated(String name) {
        Declared held = declarations.get(name);
        if (held == null || !held.stated) return false;
        put(name, held.sort, true);
        return true;
    }

    /** The sort the corpus states for this name, or null if it states none. */
    public Sort statedSort(String name) {
        Declared held = declarations.get(name);
        return held != null && held.stated ? held.sort : null;
    }

    /**
     * One name, one sort.  A second sort is refused by name (dropping the
     * path) and kept in {@link #sortConflicts} for a BLOCKING gap, never
     * thrown.  The FIRST declaration stands: re-sorting would make earlier
     * assertions ill-sorted and z3 would answer {@code (error ...)}.
     */
    private void put(String name, Sort sort, boolean stated) {
        Declared held = declarations.get(name);
        if (stated && (held == null || !held.stated)) {
            // A read of this name lowers to it from now on, not inlined.
            memo = new HashMap<MemoKey, Attempt<?>>();
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

    /** Names this corpus would give two sorts, and the two sorts. */
    public Map<String, String> sortConflicts() {
        return Collections.unmodifiableMap(root.sortConflicts);
    }

    /** Truncated minted names that would stand for two identities. */
    public Map<String, String> nameCollisions() {
        return symbols.collisions();
    }

    /** Whether the recording states a meaning for one name. */
    public boolean stated(String name) {
        Declared held = declarations.get(name);
        return held != null && held.stated;
    }

    /** Whether one name is declared in this query. */
    public boolean declared(String name) {
        Declared held = declarations.get(name);
        return held != null && held.inQuery;
    }

    /**
     * Whether this query gives one name a meaning at all: a
     * {@code declare-const} or a container subterm's {@code define-fun}.
     */
    public boolean defined(String name) {
        return declared(name) || sharedByName.containsKey(name);
    }

    /** The sort this query declares one name at, or null when it does not
     *  declare it: one lookup, not a copy of every declaration (asked per
     *  mint binding, a copy each made hdfs-11741 m1's composition
     *  quadratic in its declarations). */
    public Sort declaredSort(String name) {
        Declared held = declarations.get(name);
        return held != null && held.inQuery ? held.sort : null;
    }

    /**
     * Whether THIS LOWERING invented the name (container subterm, identity,
     * environment cell), so the query defines it.  A name off a recorded
     * leaf ({@link #usedSymbols}) means what the recording says, and an
     * unstated one must be refused, not declared free.
     */
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

    /** A refused LEAF of this Java type ({@link #leaf}). */
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

    /**
     * The sort one leaf lowers at: a container state where the codec asks
     * for one, else its own Java type's, else the one expected.
     */
    private static Sort leafSort(String javaType, Sort expected) {
        if (expected != null && expected.containerState()) return expected;
        Sort own = JavaSmtSorts.sortOfJava(javaType);
        return own != Sort.VALUE ? own : expected;
    }

    /**
     * A refused leaf: fresh, at the sort and width its node's Java type
     * states, as a stated one would be.  At the sort expected alone, a read
     * refused under a {@code ==} became VALUE and one missing value 57
     * sort conflicts, and a long cut as an int a malformed {@code lcmp}
     * (SOLR-18406 s46): one cause, one refusal.
     */
    private Term leaf(Sort expected, String javaType) {
        return free(leafSort(javaType, expected),
                JavaPrimitiveSmtSemantics.widthOfJavaType(javaType));
    }

    /**
     * One fresh unconstrained value for a refused construct: FRESH PER
     * CONSTRUCT, NEVER PER REASON.  A refusal knows nothing about the value,
     * not even equality with another refused one; sharing one variable
     * makes paths spuriously UNSAT (e.g. {@code (>= u 0)} and its negation
     * over one {@code u}).  An integral of no stated width is an int.
     */
    private Term free(Sort sort, IntegralWidth width) {
        Sort declared = sort == null || sort == Sort.UNKNOWN
                ? Sort.VALUE : sort;
        String name = symbols.mint("unsupported__",
                scope + "#" + declared + "#" + freeConstants++, 10);
        declare(name, declared);
        return Term.of(name, declared, width == IntegralWidth.NONE
                ? IntegralWidth.JAVA_INT : width);
    }

    /** How many refused constructs this lowering has named. */
    private int freeConstants;

    /** One thing this lowering states, and the label a core reads it by. */
    private static final class Stated {
        private final String formula;
        /** "" for a fact about a name; the core's label otherwise. */
        private final String label;

        private Stated(String formula, String label) {
            this.formula = formula;
            this.label = label;
        }

        private String render() {
            return label.isEmpty() ? "(assert " + formula + ")"
                    : "(assert (! " + formula + " :named " + label + "))";
        }
    }

    public void assertNamed(String name, String formula) {
        assertions.add(new Stated(formula, name));
    }

    /** Takes back the named assertions of a refused path or arm. */
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

    /**
     * The unlabeled FACTS about the names these texts reach (e.g. an
     * {@code identity__} is non-null).  A query emitting a name without its
     * facts frees a boundary variable, which is never free (PIPELINE §7.5).
     * {@link #body} emits them itself; other callers ask here.  A fact is
     * returned only if EVERY name in it is reached: half a relation is a
     * different fact.
     */
    public List<String> facts(Iterable<String> texts) {
        Set<String> reached = new LinkedHashSet<String>(SmtNames.preambleNames());
        for (Declaration declaration : reachedBy(texts)) {
            reached.add(declaration.name);
        }
        List<String> stated = new ArrayList<String>();
        for (Stated held : assertions) {
            if (!held.label.isEmpty()) continue;
            boolean whole = true;
            for (String name : SmtNames.names(held.formula)) {
                if (SmtNames.BUILTIN.contains(name) || reached.contains(name)) {
                    continue;
                }
                whole = false;
                break;
            }
            if (whole && !stated.contains(held.formula)) {
                stated.add(held.formula);
            }
        }
        return stated;
    }

    /**
     * Each propagation cut, by subject, with the detail its refusal stated
     * ("" for none).  The detail is kept under the refusal's own subject,
     * {@code PROPAGATION_CUT:<subject>}.
     */
    public Map<String, String> cuts() {
        Map<String, String> named = new LinkedHashMap<String, String>();
        for (String cut : root.cuts) {
            named.put(cut,
                    unsupportedDetail.getOrDefault(CUT + ":" + cut, ""));
        }
        return named;
    }

    /**
     * Each method-return symbol pinned to the value its node states, with
     * that value: a dependency the formula carries only as the named pin.
     */
    public Map<String, String> pinnedReturns() {
        return Collections.unmodifiableMap(root.pinnedReturns);
    }

    /**
     * Each value COMPOSE could not bind to the expression that made it, in
     * the order met, by THE ONE RULE ({@link #bind}, {@link #methodReturn},
     * {@code Composer#arrival}): FREE where the producer the rows state
     * rests on what can move -- the formula over-approximates it, and a
     * witness resting on it is CONFIRM's to refute -- else HELD at its
     * recorded value where no row states its producer.  Never free by
     * default, never a silent pin.  Information, never a gap; a composer
     * keeps those its admitted paths made ({@code Composer#concrete}).
     */
    public List<Unbound> unbound() {
        return Collections.unmodifiableList(root.unbound);
    }

    /** One value COMPOSE could not bind ({@link #unbound}). */
    public static final class Unbound {
        /** A free value over what it rests on. */
        public static final String FREE = "FREE";
        /** A value held at what the recording states. */
        public static final String HELD = "HELD";
        /** Why a HELD value is held. */
        public static final String PRODUCER_UNSTATED = "producer unstated";

        /** {@link #FREE} or {@link #HELD}. */
        public final String kind;
        public final String subject;
        /** A HELD value's recorded value; "" for a FREE one. */
        public final String value;
        /** Why it is unbound, in words. */
        public final String reason;
        /** What a FREE value rests on that can move. */
        public final List<String> movesWith;
        /** The arm whose body left it unbound, "" for a path's own. */
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

    /** An arrival nothing binds or pins, left FREE ({@link #unbound}):
     *  its producer attested and no export of it lowered, or its row's
     *  value no term ({@code Composer#arrival}). */
    public void freedArrival(String symbol, String why) {
        freed(symbol, why, Collections.<String>emptySet());
    }

    /**
     * A value held at what the recording states because no row states its
     * producer ({@link #unbound}): a composer's pin of a read whose version
     * no write states, or of an arrival no producer this corpus attests.
     */
    public void held(String subject, String value, String why) {
        top().unbound.add(new Unbound(Unbound.HELD, subject, value,
                Unbound.PRODUCER_UNSTATED + ": " + why,
                Collections.<String>emptyList(), arm));
    }

    /**
     * One name this query gives a meaning, and how.
     *
     * <p>{@code body} empty is a {@code declare-const}; otherwise it is the
     * body of a {@code define-fun} of that sort.</p>
     */
    public static final class Declaration {
        public final String name;
        public final String sort;
        public final String body;

        private Declaration(String name, String sort, String body) {
            this.name = name;
            this.sort = sort;
            this.body = body;
        }

        /** This declaration as one line of SMT-LIB. */
        public String render() {
            return body.isEmpty()
                    ? "(declare-const " + name + " " + sort + ")"
                    : "(define-fun " + name + " () " + sort + " " + body
                    + ")";
        }
    }

    /**
     * Exactly the declarations these texts reach (through subterm bodies, to
     * a fixed point), dependencies first.  A cached lowering holds names
     * from terms the query does not conjoin; those must not be emitted.
     */
    public List<Declaration> reachedBy(Iterable<String> texts) {
        List<Declaration> ordered = new ArrayList<Declaration>();
        Set<String> done = new LinkedHashSet<String>();
        if (texts != null) {
            for (String text : texts) {
                reach(text, done, ordered);
            }
        }
        return ordered;
    }

    /**
     * One text's declarations, a subterm after the ones its body names, on a
     * stack: a container's mutation chain is one subterm per mutation, and
     * a cap at depth 512 left the deeper ones undeclared.
     */
    private void reach(String text, Set<String> done,
                       List<Declaration> ordered) {
        if (text == null || text.isEmpty()) return;
        List<Iterator<String>> names = new ArrayList<Iterator<String>>();
        // The subterm each level of names is the body of; null for the text.
        List<SharedTerm> bodies = new ArrayList<SharedTerm>();
        names.add(SmtNames.names(text).iterator());
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
            SharedTerm shared = sharedByName.get(token);
            if (shared != null) {
                // Its own dependencies first: a define-fun may name another.
                names.add(SmtNames.names(shared.body).iterator());
                bodies.add(shared);
                continue;
            }
            Declared held = declarations.get(token);
            if (held != null && held.inQuery) {
                ordered.add(new Declaration(token, held.sort.smt, ""));
            }
        }
    }

    /**
     * The recording's symbols these texts SAY, together, THROUGH the
     * container subterms they name (same reachability as {@link
     * #reachedBy}); minted names are walked through, never reported.  A
     * guard over a map read is just {@code container_dag__...}, so the text
     * alone names nothing.  What a term RESTS ON is the closure's question,
     * asked of the expressions, not of their text ({@code
     * Corpus#expressionSymbols}).
     */
    public Set<String> reachedSymbols(Iterable<String> texts) {
        Set<String> into = new LinkedHashSet<String>();
        Set<String> seen = new LinkedHashSet<String>();
        for (String text : texts) reachedSymbols(text, seen, into);
        return into;
    }

    /** On a stack, as {@link #reach}: capped at depth 512, a mutation chain
     *  hid the symbols of its deeper subterms. */
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
            SharedTerm shared = sharedByName.get(name);
            if (shared != null) {
                names.push(SmtNames.names(shared.body).iterator());
                continue;
            }
            // Only recorded names can be asked of the corpus.
            if (minted(name)) continue;
            into.add(name);
        }
    }

    /** The preamble alone: the sorts and functions, no declaration. */
    public List<String> preambleLines() {
        List<String> lines = new ArrayList<String>();
        lines.add("(set-logic ALL)");
        lines.add("(set-option :produce-models true)");
        for (String line : VmTermLowering.preamble()) lines.add(line);
        // Offered always: a query keeps only the definitions it reaches
        // (SmtNames#reachedPreamble), and an integral's String.valueOf is
        // lowered through it.
        lines.add(VmTermLowering.JAVA_INT_TO_STRING);
        lines.add(JavaPrimitiveSmtSemantics.INT_WRAP_DEFINITION);
        lines.add(JavaPrimitiveSmtSemantics.LONG_WRAP_DEFINITION);
        return lines;
    }

    private void appendPreamble(StringBuilder query,
                                Iterable<String> texts) {
        query.append("; GraphChecker composed query").append('\n');
        // No core tracking: the one run asking for a core sets it
        // (Z3#CORE_TRACKING).  Only the part of the one preamble the query
        // reaches.
        for (String line : SmtNames.reachedPreamble(preambleLines(), texts)) {
            query.append(line).append('\n');
        }
    }

    /**
     * The query body (preamble, declarations, assertions; no check-sat),
     * declaring only what the assertions and
     * {@code alsoAsked} reach ({@link #reachedBy}); names left by dropped
     * questions are not declared.
     *
     * <p>{@code alsoAsked} is text the body will be asked with but does not
     * contain (the valuation pins); it is reached for declaration, not
     * appended ({@link Composition#query} appends it).</p>
     */
    public String body(Iterable<String> alsoAsked) {
        List<String> texts = new ArrayList<String>();
        for (Stated held : assertions) texts.add(held.formula);
        if (alsoAsked != null) {
            for (String text : alsoAsked) {
                if (text != null && !text.isEmpty()) texts.add(text);
            }
        }
        // Declarations first: the preamble needed is decided by their
        // bodies too, not just the assertions.
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

    // ------------------------------------------------------------------
    // Reading a recorded location out of a VM node.
    // ------------------------------------------------------------------

    /**
     * The join key of one recorded location.  Must spell exactly as
     * {@link #locationKey(JsonObject)} does, or every state join misses.
     */
    public static String locationKey(LocationId location) {
        return location == null ? "" : location.kind() + "/"
                + location.owner() + "#" + location.slot();
    }

    /** The join key of one VM location node, in the same spelling. */
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
        return locationKey(LocationId.of(locationKind(kind), owner, slot));
    }

    private static LocationKind locationKind(String kind) {
        String value = kind.toUpperCase();
        if (value.startsWith("STATIC")) return LocationKind.STATIC;
        if (value.startsWith("ARRAY")) return LocationKind.ARRAY;
        if (value.startsWith("MAP")) return LocationKind.MAP;
        return LocationKind.INSTANCE;
    }

    /**
     * The version's value as the read itself saw it, or null.
     *
     * <p>Read only where a row states the version: see
     * {@link #guardedReadTerm}.</p>
     */
    private static JsonElement observedVersionExpression(JsonObject node) {
        if (!VmRows.joinable(node)) return null;
        JsonElement observed = node.get(VmRows.OBSERVED_VERSION);
        if (observed == null || !observed.isJsonObject()) return null;
        return observed.getAsJsonObject().get("expression");
    }

    private static long observedVersion(JsonObject node) {
        return VmRows.joinable(node) ? VmRows.recordedVersion(node) : -1L;
    }

    /** What separates the parts of a minted name's identity. */
    private static final String SEPARATOR = "|";

    // ------------------------------------------------------------------
    // Dispatch.
    // ------------------------------------------------------------------

    /**
     * Lowers one recorded VM expression of any kind.  Never null: a refused
     * construct is a fresh value of its sort, named in the open refusals.
     */
    public Term dispatch(JsonElement expression, Sort expected,
                        String origin) {
        return memoized(expression, expected, () -> {
            Term value = lowered(expression, expected, origin);
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
        if ("NotExpression".equals(type)) {
            Term operand = dispatch(object.get("_operand"), Sort.BOOL,
                    origin + ":not");
            if (operand.sort != Sort.BOOL) {
                return refuse(Reason.MALFORMED_NOT, origin, "", Sort.BOOL);
            }
            return result("(not " + operand.text + ")", Sort.BOOL, operand);
        }
        if ("PlaceholderExpression".equals(type)) {
            return placeholderTerm(object);
        }
        if ("TypeCastExpression".equals(type)) {
            return typeCast(object, origin);
        }
        if (VmRows.GUARDED_READ_TYPE.equals(type)) {
            return guardedReadTerm(object, expected, origin);
        }
        if (VmExpressionIr.consumerBoundary(object)) {
            // Outside final composition an anchor is the value the VM
            // propagated.
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

    /**
     * A Java library call: a callee this lowering knows is its relation
     * ({@link #knownCall}), a split element its piece of a template
     * ({@link StringIdentities#splitElement}); any other is a named gap at
     * the sort the call returns.
     */
    private Term methodTerm(JsonObject expression, String origin) {
        String method = optionalString(expression, "_name");
        Term related = knownCall(method, array(expression, "_param_list"),
                origin);
        if (related != null) return related;
        if (VmExpressionIr.isJavaSplitElement(method)) {
            JsonElement element = StringIdentities.splitElement(expression);
            return element != null
                    ? dispatch(element, null, origin + ":split-element")
                    : refuse(Reason.MODEL_SEMANTICS_MISSING, origin,
                    "java/lang/String.splitElement", Sort.STRING);
        }
        Term result = dispatch(expression.get("_res_exp"), null, origin);
        return refuse(Reason.MODEL_SEMANTICS_MISSING, origin,
                "MethodExpression:" + firstNonBlank(method, "unknown"),
                result.sort);
    }

    // ------------------------------------------------------------------
    // Binary operators.
    // ------------------------------------------------------------------

    /**
     * An integral constant compared with an instant of a clock cell this
     * session's host read off the recording's timeline, moved onto it: an
     * instant is compared only with an instant, so the constant is one, on
     * this session's clock ({@link #clockBases}).  Anything else as it is.
     */
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

    /**
     * The clock cell an integral term is an instant of: the cell itself, or
     * an instant plus or minus a constant span (a Java wrap around either
     * keeps it); "" for anything else, a difference of two instants
     * included.
     */
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

    /** One recorded {@code BinaryExpression}. */
    private Term binary(JsonObject expression, String origin) {
        String operator = JavaPrimitiveSmtSemantics.canonicalVmOperator(
                optionalString(expression, "_op"));
        JsonElement leftExpression = expression.get("_left");
        if (leftExpression == null || leftExpression.isJsonNull()) {
            return unary(expression, operator, origin);
        }
        // One operand is asked at the other's sort; a named object is the
        // one asked, on either side (an identity beside a reference).
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
        // A JVM reference comparison against the integer 0 is a null test.
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
            // lcmp is typed long: a widthless int operand is a long.
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
            // Refused at the int its bytecode promises (free INT is an int).
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
        if (left.sort != right.sort && equality
                && (left.isNullReference() || right.isNullReference())) {
            // Java primitives are never null.
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
            // One side is a boxed cell: unbox it by its declared type.
            // Reference or unknown cells stay boxed and are refused below.
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

    /**
     * Java {@code ==} between two Strings is reference identity.  Two
     * cases close it exactly and the rest stays refused.
     */
    private Term stringIdentity(JsonObject expression, String operator,
                                Term left, Term right, String origin) {
        if (!left.stringReferenceOrigin.isEmpty()
                && left.stringReferenceOrigin.equals(
                right.stringReferenceOrigin)) {
            return result("!=".equals(operator) ? "false" : "true",
                    Sort.BOOL, left, right);
        }
        // Against an interned String literal, identity is content equality.
        // With no literal on either side it would over-approximate, so it
        // stays refused.
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
            // SMT's fp.rem is the IEEE remainder, which rounds the
            // quotient to even where Java's % truncates it.
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
            // Java truncates toward zero; a zero divisor throws, so it is
            // the operation's definedness, not a solver choice.
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

    // ------------------------------------------------------------------
    // Constants.
    // ------------------------------------------------------------------

    /** One recorded constant expression. */
    private Term constant(JsonObject expression, Sort expected,
                          String origin) {
        String raw = optionalString(expression, "_exp");
        String javaType = optionalString(expression, "_java_type");
        String value = constantPayload(raw);
        Sort sort = JavaSmtSorts.sortOfJava(javaType);
        // A JVM boolean is recorded as an int; only 0 and 1 are accepted.
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

    // ------------------------------------------------------------------
    // String operations.
    // ------------------------------------------------------------------

    /** One recorded {@code OpStrExpression}. */
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
                || "lastIndexOf".equals(operation)) {
            if (negated) {
                return codecGap(operation, "NEGATED_VALUE_OPERATION", origin,
                        Sort.INT);
            }
            return stringPosition(operation, params, origin);
        }
        if ("equals".equals(operation)) {
            return stringEquals(params, negated, origin);
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
        if ("substring".equals(operation)) {
            return substring(params, origin);
        }
        if ("trim".equals(operation)) {
            return trim(params, origin);
        }
        if ("toString".equals(operation)) {
            return javaToString(params, origin);
        }
        return codecGap(firstNonBlank(operation, "unknown"),
                "UNSUPPORTED_OPERATION", origin, Sort.STRING);
    }

    /**
     * The String form of one value: a String is itself; a char is its one
     * character; byte, short, int and long are decimal (the file names that
     * carry a block's id and generation stamp, blk_<id>_<gs>.meta), as is a
     * binary operator's value, an int or a long whatever its width; a
     * boolean is {@code "true"} or {@code "false"}.
     */
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
        assertJavaIntegralDomain(value.text, javaType);
        if ("C".equals(javaType)) {
            return Term.nonNullString("(str.from_code " + value.text + ")",
                    value.precondition);
        }
        return Term.nonNullString("(java_int_to_string " + value.text + ")",
                value.precondition);
    }

    private static final Set<String> DECIMAL_OR_CHAR = new LinkedHashSet<String>(
            Arrays.asList("B", "S", "I", "J", "C"));

    /**
     * String.trim(): what lies between a fresh begin and end, every
     * character outside them at most U+0020 and, unless none is left, the
     * first and the last inside above it -- so the cut is Java's (b20h
     * BlockRecoveryWorker-222: the InterDatanodeProtocol proxy's URI,
     * {@code "dummyscheme://" + (ip + ":" + port).trim()}, refused every
     * value parsed from it).
     */
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

    /** How many trims this lowering has named. */
    private int trims;

    /** String.substring(b) and (b, e), defined where Java does not throw:
     *  0 <= b <= e <= length. */
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

    /**
     * charAt(i), indexOf(x) and lastIndexOf(x), x a char or a String, as
     * Java answers them.  z3 has no last index: it is a fresh k that only
     * the last occurrence satisfies -- x at k and none after it, -1 and none
     * at all, or the length for an empty x.
     */
    private Term stringPosition(String operation, JsonArray params,
                                String origin) {
        if (params.size() != 2) {
            return codecGap(operation, "ARITY", origin, Sort.INT);
        }
        Term receiver = dispatch(params.get(0), null,
                origin + ":" + operation + ":receiver");
        Term argument = dispatch(params.get(1), null,
                origin + ":" + operation + ":argument");
        if (receiver.sort != Sort.STRING || (argument.sort != Sort.INT
                && ("charAt".equals(operation)
                || argument.sort != Sort.STRING))) {
            return codecGap(operation, "PARAMETER_SORT", origin, Sort.INT);
        }
        if (nullnessUnknown(Arrays.asList(receiver, argument))) {
            return refuse(Reason.JAVA_STRING_NULLNESS_UNKNOWN, origin,
                    operation, Sort.INT);
        }
        String text = receiver.text;
        String length = "(str.len " + text + ")";
        if ("charAt".equals(operation)) {
            String index = argument.text;
            String code = "(str.to_code (str.at " + text + " " + index + "))";
            assertJavaIntegralDomain(code, "C");
            return definedResult(code, Sort.INT, IntegralWidth.JAVA_INT,
                    and(Arrays.asList(stringDefinedness(
                                    Collections.singletonList(receiver),
                                    Collections.singletonList(argument)),
                            "(<= 0 " + index + ")",
                            "(< " + index + " " + length + ")")));
        }
        boolean character = argument.sort == Sort.INT;
        String needle = character ? "(str.from_code " + argument.text + ")"
                : argument.text;
        String defined = character
                ? stringDefinedness(Collections.singletonList(receiver),
                        Collections.singletonList(argument))
                : stringDefinedness(Arrays.asList(receiver, argument),
                        Collections.<Term>emptyList());
        if ("indexOf".equals(operation)) {
            return definedResult("(str.indexof " + text + " " + needle
                    + " 0)", Sort.INT, IntegralWidth.JAVA_INT, defined);
        }
        String last = symbols.mint("last_index_of__",
                scope + "#" + lastIndexes++, 10);
        declare(last, Sort.INT);
        sideCondition("(or (and (= " + needle + " \"\") (= " + last + " "
                + length + ")) (and (not (= " + needle + " \"\")) (= "
                + last + " (- 1)) (not (str.contains " + text + " " + needle
                + "))) (and (not (= " + needle + " \"\")) (<= 0 " + last
                + ") (= (str.substr " + text + " " + last + " (str.len "
                + needle + ")) " + needle + ") (not (str.contains (str.substr "
                + text + " (+ " + last + " 1) " + length + ") " + needle
                + "))))");
        return definedResult(last, Sort.INT, IntegralWidth.JAVA_INT, defined);
    }

    /** How many last indexes this lowering has named. */
    private int lastIndexes;

    /** What a boolean rendering compared with a literal is, over the flag. */
    private static String truth(StringIdentities.BooleanTest test, Term flag) {
        return test.truth == StringIdentities.Truth.FLAG ? flag.text
                : test.truth == StringIdentities.Truth.NEGATED
                ? "(not " + flag.text + ")" : "false";
    }

    /**
     * Java String.equals requires a non-null receiver but accepts null.  A
     * rendering compared as text is compared as the value it renders
     * ({@link StringIdentities#booleanTest}, {@link
     * StringIdentities#pieceWise}), within the same definedness.
     */
    private Term stringEquals(JsonArray params, boolean negated,
                              String origin) {
        if (params.size() != 2) {
            return codecGap("equals", "ARITY", origin, Sort.BOOL);
        }
        Term receiver = dispatch(params.get(0), null,
                origin + ":equals:parameter0");
        Term argument = dispatch(params.get(1), null,
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

    /**
     * Two lowered Strings' equality as the values their renderings render,
     * else {@code text}.  Both sides are lowered already, so every piece
     * lowered here was lowered with them.
     */
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

    /**
     * The parameters of one String operation, each of them a String, or
     * the refusal once the arity or a parameter's sort refused it.
     */
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
            // No expected sort: STRING would declare a malformed primitive
            // leaf as String.  Check the derived sort instead.
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

    /**
     * Either every parameter as a String term and where the operation is
     * defined over them, or ({@code terms} null) the refusal.
     */
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

    /** "true" when this String is known non-null, else the negated Bool. */
    private static String stringNonNull(Term term) {
        if (term.sort != Sort.STRING) return "false";
        return "false".equals(term.stringNullness) ? "true"
                : "(not " + term.stringNullness + ")";
    }

    /** One String operation this lowering could not close. */
    private Term codecGap(String operation, String gap, String origin,
                          Sort sort) {
        return refuse(Reason.MODEL_SEMANTICS_MISSING, origin,
                "OpStrExpression." + operation + ":" + gap, sort);
    }

    // ------------------------------------------------------------------
    // Boxed container cells.
    // ------------------------------------------------------------------

    /** Unboxes one container cell by the element's declared Java type. */
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
            // `defined` checks the VString tag, so this is non-null.
            return Term.nonNullString("(valueString " + value.text + ")",
                    defined);
        }
        return value;
    }

    // ------------------------------------------------------------------
    // Small shared predicates.
    // ------------------------------------------------------------------

    /** Java binary numeric promotion of two integral operands. */
    private static IntegralWidth promotedIntegralWidth(Term left,
                                                       Term right) {
        if (left.sort != Sort.INT || right.sort != Sort.INT) {
            return IntegralWidth.NONE;
        }
        return JavaPrimitiveSmtSemantics.promote(left.integralWidth,
                right.integralWidth);
    }

    /** The String this expression is exactly a literal of, or null. */
    private static String stringLiteral(JsonElement expression) {
        return VmExpressionIr.exactStringLiteral(expression,
                type -> JavaSmtSorts.sortOfJava(type) == Sort.STRING);
    }

    /** Java binary numeric promotion of one operand to a floating sort. */
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

    /** One JVM primitive conversion; every other cast is a named gap. */
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
        // Every non-primitive cast produces a reference.
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
