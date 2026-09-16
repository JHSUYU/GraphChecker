package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.JsonFields;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.smt.VmRows;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.IntegralWidth;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Term;
import edu.uva.liftlab.graphchecker.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Collection;
import java.util.Set;
import java.util.function.Predicate;

import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.smtLiteral;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.primitiveString;

/**
 * The ONE SMT lowering: the composer's and the flip solver's.
 *
 * <p>Two hosts of one expression vocabulary is how the composed query and
 * the flip query came to disagree about a field projection, about a
 * container cell's Java width, and about which symbol names which root.
 * There is one host here, and the three policies it states -- what a leaf
 * may be, what a read joins to, and where a definedness fact is conjoined
 * -- are stated once.</p>
 *
 * <p>What a leaf can be is fixed by the recording and nothing else:</p>
 * <ul>
 *   <li>a DECLARED symbol -- a root the case minted, a handoff variable
 *       v_H an attach minted, or a clock cell a decision read -- lowered to
 *       the name the runtime published it under, because the decision terms
 *       and phi the runtime publishes are written over those names and a
 *       renaming here would silently make two formulas about two different
 *       variables;</li>
 *   <li>an execution-local IDENTITY (which object this replay ran on),
 *       opaque, per session, asserted non-null and distinct from the other
 *       identities of its own session -- both recorded facts;</li>
 *   <li>a literal, or a container relation over those.</li>
 * </ul>
 *
 * <p>Anything else is the propagation cut, refused under that name rather
 * than answered by minting something free.</p>
 */
public final class SmtLowering extends VmLoweringCore {

    /** The refusal that means "propagation did not carry the value". */
    public static final String CUT = "PROPAGATION_CUT";
    /** The refusal that means "the recording states no value here". */
    public static final String UNSTATED = "UNSTATED_VALUE";
    /** The refusal that means "one solver name, two sorts". */
    public static final String SORT_CONFLICT = "SORT_CONFLICT";
    /** How a published term names an expression of the session's table. */
    private static final String REFERENCE = "EXPR.";
    /** How deep a reference may stand for text naming another reference. */
    private static final int REFERENCE_ROUNDS = 4;

    /**
     * The write log of one session, as the state join reads it.
     *
     * <p>A read is joined to the expression of the write version it
     * observed, WITHIN ITS OWN SESSION -- versions are session-local
     * counters, and a cross-session join would state one replay's history
     * of another replay's object.</p>
     */
    public interface SessionJoin {
        /** The write expression at this location and version, or null. */
        JsonElement writeExpression(String locationKey, long version);

        /**
         * The symbols this session's placeholder ROWS state for the
         * version the mint gave the read.
         *
         * <p>A declared region input is a READ, so the mint's shadow store
         * is no write and no {@code WriteRow} states the version it
         * created -- but a term's {@code ReadFromExpression} names exactly
         * that version, because that is what the location held when the
         * read ran.  {@code ReadRow.mintVersion} (CONTRACT v2.4) is that
         * version, and it is what the reader and the row are matched by:
         * unique by construction, where {@code (occurrence, location)} was
         * not -- one occurrence may declare one cell under SEVERAL ports,
         * and laneA4 failed on exactly that, two placeholder rows of one
         * occurrence for {@code INSTANCE/2#24} refusing each other.</p>
         */
        Set<String> mintedReadSymbols(long version);

        /**
         * The symbols this session's READ ROWS state for reads of one
         * location at one version.
         *
         * <p>The join INLINES: a read of a version the write log covers
         * lowers to the writer's own propagation, so the read's own symbol
         * -- the name the ROW gives what the location held at that version
         * -- stands nowhere in the lowered text.  For a scalar that is
         * harmless, because the inlined chain ends at the recording's
         * leaves; for a CONTAINER it is not, because the chain is named
         * once as a {@code container_dag__} and the state it stands for is
         * a version, not a leaf.  This is the row that names it, so that
         * {@link #reachedSymbols} can answer "which recorded state is this
         * subterm the value of" out of the recording rather than by
         * re-spelling the runtime's name.</p>
         *
         * <p>Placeholder rows are not here: a mint states a symbol for the
         * version the MINT created ({@link #mintedReadSymbols}), and its
         * {@code observedVersion} is the last real write it was laid over
         * -- naming it here would put the minted value on the write's own
         * readers.</p>
         */
        Set<String> readSymbols(String locationKey, long version);
    }

    private static final SessionJoin NO_JOIN = new SessionJoin() {
        @Override
        public JsonElement writeExpression(String locationKey, long version) {
            return null;
        }

        @Override
        public Set<String> mintedReadSymbols(long version) {
            return Collections.<String>emptySet();
        }

        @Override
        public Set<String> readSymbols(String locationKey, long version) {
            return Collections.<String>emptySet();
        }
    };

    /**
     * What each MINT VERSION of a session is worth, by that version.
     *
     * <p>The index every view of a session builds, so that "which symbol
     * did the mint at this version give the read" has ONE answer however
     * the session was opened.  A row counts when it states a mint version
     * and a symbol: its symbol is then bound by that row's own JOIN or
     * PIN, which is what makes it usable as the value of a read of the
     * version the mint created.</p>
     *
     * <p>{@code ReadRow.mintVersion} is unique by construction, so no
     * scope is needed and none is taken: the (occurrence, location) bridge
     * this replaces could not tell two ports of one occurrence apart and
     * refused them both.</p>
     */
    public static Map<Long, Set<String>> mintedReadIndex(
            Iterable<ReadRow> reads) {
        Map<Long, Set<String>> minted =
                new LinkedHashMap<Long, Set<String>>();
        if (reads == null) return minted;
        for (ReadRow read : reads) {
            if (read == null || read.mintVersion() < 0L) continue;
            if (read.symbol() == null || read.symbol().isEmpty()) continue;
            Long key = Long.valueOf(read.mintVersion());
            Set<String> symbols = minted.get(key);
            if (symbols == null) {
                symbols = new LinkedHashSet<String>();
                minted.put(key, symbols);
            }
            symbols.add(read.symbol());
        }
        return minted;
    }

    /**
     * The one symbol the mint at this version gave the read.
     *
     * <p>{@code ""} when no row states one.  Rows that disagree state NO
     * answer -- {@code null} -- and every caller refuses that by name: the
     * mint version is unique by construction, so two symbols under one of
     * them is the recording contradicting itself, and picking either would
     * put one read's value on another read.</p>
     */
    public static String mintedReadSymbol(SessionJoin join, long version) {
        Set<String> symbols = join == null || version < 0L
                ? null : join.mintedReadSymbols(version);
        if (symbols == null || symbols.isEmpty()) return "";
        if (symbols.size() > 1) return null;
        return symbols.iterator().next();
    }

    private final SmtSymbolTable symbols = new SmtSymbolTable();
    /**
     * Every name this query gives a meaning to: ONE registry.
     *
     * <p>There is one notion -- what declares a name -- and it used to be
     * kept in two maps: what the recording states, read by the leaf
     * lowering, and what the query declares, written by {@link #declare}.
     * A symbol a ReadRow states was written into the second and looked up
     * in the first, so the join or pin bound the NAME while every leaf
     * naming it was cut as free: 18 {@code PROPAGATION_CUT} rows on the
     * 17960 anchor and the path with them, beside a
     * {@code (declare-const M_I_field_... Int)} in the same file.</p>
     */
    private final Map<String, Declared> declarations =
            new LinkedHashMap<String, Declared>();
    /** What this corpus states at two sorts: name -> "<held> and <new>". */
    private final Map<String, String> sortConflicts =
            new LinkedHashMap<String, String>();
    /**
     * Everything this lowering states, as {@link Stated} and not as
     * finished {@code (assert ...)} lines.
     *
     * <p>Two kinds, and the entry says which: a FACT about a name -- an
     * identity the execution read fields off was not null, an integral leaf
     * inside its Java domain, a container subterm at the cell shape it was
     * built at -- and a question the COMPOSITION labels for its own unsat
     * core.  A caller assembling a query of its own takes the facts its
     * text reaches ({@link #facts}) and never the labels, which it could
     * not tell apart when the list held finished lines.</p>
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
     * The same subterms by the NAME they were minted under.
     *
     * <p>{@link #sharedTerms} is keyed by the digest of the definition,
     * which is what dedupes them; every reader asks the other question --
     * "what stands behind this name" -- and each rebuilt its own map or
     * scanned the values to answer it.  One index, built where the name is
     * minted.</p>
     */
    private final Map<String, SharedTerm> sharedByName =
            new LinkedHashMap<String, SharedTerm>();
    private final Set<String> unsupported = new LinkedHashSet<String>();
    private final Map<String, String> unsupportedDetail =
            new LinkedHashMap<String, String>();
    private final Set<String> cuts = new LinkedHashSet<String>();
    private final Set<String> integralDomains = new LinkedHashSet<String>();
    private boolean usesJavaIntString;

    /**
     * Where a symbol's declaration comes from.
     *
     * <p>Two authorities, one algorithm.  A CORPUS lowering knows every
     * symbol the runtime declared across the sessions, so a scalar leaf
     * outside that set is the propagation cut and is refused by name.  A
     * SESSION lowering is handed one expression and nothing else, so the
     * mint's own {@code _java_type} on the leaf is what declares it.  The
     * difference is which recording states the declaration, never how the
     * expression is lowered.</p>
     */
    private final boolean symbolsDeclareThemselves;
    /** The session's expression table, for {@link #lower(String)}. */
    private final ExpressionTable table;

    /** Side conditions the conjunction now open raised, or null. */
    private List<String> openSideConditions;
    private List<String> openRefusals;
    private String scope = "";
    private SessionJoin join = NO_JOIN;
    /** The expression table of the session whose conjunction is open. */
    private ExpressionTable openTable;
    /** The conjunctions a nested lowering interrupted, innermost first. */
    private final java.util.Deque<Frame> frames =
            new java.util.ArrayDeque<Frame>();

    /** The lowering of one CORPUS: its rows declare every symbol. */
    public SmtLowering(Map<String, Sort> declaredSymbols) {
        this(declaredSymbols, false, null);
    }

    private SmtLowering(Map<String, Sort> declaredSymbols,
                        boolean symbolsDeclareThemselves,
                        ExpressionTable table) {
        // The corpus's own statements, in the one registry, not yet in the
        // query: a name the recording declares becomes a declaration of
        // THIS query when the query names it, and not before -- which is
        // what `declared` answers and what the preamble emits.
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
     * One name's declaration: its sort, who states it, and whether the
     * query has named it.
     *
     * <p>Two facts, one entry.  {@code stated} is the recording's: a root
     * mint, a clock reading, an attach, or a read row of a session says
     * this name means something, so a {@code SymbolExpression} leaf
     * naming it lowers to it rather than being cut as free.
     * {@code inQuery} is this query's: the formula names it, so the
     * preamble declares it and {@code declared} answers yes.</p>
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
     * The lowering of ONE session's expressions, by reference.
     *
     * <p>What the flip solver needs: hand it a session's expression table,
     * ask it for the SMT text of one {@code expressionRef}, and it answers
     * with the text and the symbols the text names -- or with the refusal
     * that stopped it.  It is the same lowering the composer runs, which is
     * the point: a flip query and the composed query must not be able to
     * disagree about a container relation or a field projection.</p>
     */
    public static SmtLowering of(ExpressionTable expressions) {
        return new SmtLowering(Collections.<String, Sort>emptyMap(), true,
                expressions);
    }

    /** The same, reading the table and the write log off one session. */
    public static SmtLowering forSession(SessionReader session) {
        SmtLowering lowering = of(session == null ? null
                : session.expressions());
        if (session != null) {
            lowering.scope = session.sessionId();
            lowering.join = joinOf(session);
        }
        return lowering;
    }

    /**
     * One session's write log and read rows, as the state join reads them.
     *
     * <p>One view per session and no scope inside it: the write log is the
     * session's, because versions are session-local counters, and a mint
     * version is unique in it by construction.  The composer asks for it by
     * session too -- it used to build a second one off its own index of the
     * same rows -- so there is one implementation of "what this session's
     * rows are worth to a join", and a session nobody read answers nothing
     * rather than throwing.</p>
     */
    public static SessionJoin joinOf(final SessionReader session) {
        if (session == null) return NO_JOIN;
        final Map<String, String> writes = new LinkedHashMap<String, String>();
        for (edu.uva.liftlab.graphchecker.contract.WriteRow write
                : session.writes()) {
            writes.put(locationKey(write.location()) + "#" + write.version(),
                    write.expressionRef());
        }
        final Map<Long, Set<String>> minted =
                mintedReadIndex(session.reads());
        final Map<String, Set<String>> observed =
                new LinkedHashMap<String, Set<String>>();
        for (ReadRow read : session.reads()) {
            if (read == null || read.mintVersion() >= 0L) continue;
            if (read.observedVersion() < 0L) continue;
            if (read.symbol() == null || read.symbol().isEmpty()) continue;
            String at = locationKey(read.location()) + "#"
                    + read.observedVersion();
            Set<String> symbols = observed.get(at);
            if (symbols == null) {
                symbols = new LinkedHashSet<String>();
                observed.put(at, symbols);
            }
            symbols.add(read.symbol());
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
        };
    }

    /**
     * One expression of this session, lowered, or a named refusal.
     *
     * <p>The declarations it answers with are the symbols its own text
     * names, at the sorts this lowering gave them: a caller that puts the
     * text in a query of its own declares exactly those and no more.</p>
     */
    public Lowered lower(String expressionRef) {
        JsonObject expression = expressionRef == null ? null
                : table.expression(expressionRef);
        if (expression == null) {
            return Lowered.refused("ABSENT_EXPRESSION:" + expressionRef);
        }
        List<String> refusalsBefore =
                new ArrayList<String>(unsupported);
        Term value = dispatch(expression, null, "lower:" + expressionRef);
        List<String> refused = new ArrayList<String>(unsupported);
        refused.removeAll(refusalsBefore);
        if (value == null || !refused.isEmpty()) {
            return Lowered.refused(refused.isEmpty()
                    ? "ABSENT_EXPRESSION:" + expressionRef : refused.get(0));
        }
        Map<String, String> named = new LinkedHashMap<String, String>();
        for (Map.Entry<String, Sort> declaration
                : declarations().entrySet()) {
            if (mentions(value.text, declaration.getKey())) {
                named.put(declaration.getKey(), declaration.getValue().smt);
            }
        }
        return new Lowered(value.text, value.sort.smt, "", named);
    }

    /**
     * One published term, with every expression REFERENCE it names lowered.
     *
     * <p>A row's {@code term} -- a decision's predicate, a target's phi --
     * is SMT text over the names the runtime published, and one of those
     * spellings is a REFERENCE into the session's expression table: the VM
     * propagates values as a shared DAG, so a branch over a propagated
     * value is published as {@code (not EXPR.1f3c6978d870b1bc)} rather
     * than as the tree that stands behind it.  Lowering it HERE, through
     * the same routine that lowers an export's {@code expressionRef}, is
     * what makes pi and phi the same expressions the deliveries are.  The
     * alternative -- treating {@code EXPR.<ref>} as a free name -- puts the
     * whole propagation outside the formula and refuses every path that
     * carries one, which is what it did.</p>
     *
     * <p>Answered "" when the lowering refused: a reference the session's
     * table does not hold is {@code UNSTATED_VALUE} by the reference's own
     * name, and a caller that cannot state a conjunct must not keep the
     * rest of it.</p>
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

    /** One pass: every reference token of this text, lowered in place. */
    private String expand(String term, String origin) {
        StringBuilder text = new StringBuilder();
        int index = 0;
        while (index < term.length()) {
            char value = term.charAt(index);
            if (!symbolCharacter(value)) {
                text.append(value);
                index++;
                continue;
            }
            int end = index;
            while (end < term.length()
                    && symbolCharacter(term.charAt(end))) {
                end++;
            }
            String token = term.substring(index, end);
            index = end;
            if (!reference(token)) {
                text.append(token);
                continue;
            }
            String lowered = loweredReference(token, origin);
            if (lowered.isEmpty()) return "";
            text.append(lowered);
        }
        return text.toString();
    }

    /** Whether one token is an expression reference: EXPR. and 16 hex. */
    static boolean reference(String token) {
        if (token == null || !token.startsWith(REFERENCE)) return false;
        String digest = token.substring(REFERENCE.length());
        if (digest.length() != 16) return false;
        for (int index = 0; index < digest.length(); index++) {
            char value = digest.charAt(index);
            boolean hex = value >= '0' && value <= '9'
                    || value >= 'a' && value <= 'f';
            if (!hex) return false;
        }
        return true;
    }

    /** One reference, lowered in the open session's scope, or "". */
    private String loweredReference(String reference, String origin) {
        ExpressionTable expressions = openTable == null ? table : openTable;
        JsonObject expression = expressions == null ? null
                : expressions.expression(reference);
        if (expression == null) {
            refuse(UNSTATED + ":" + reference,
                    "a published term names this expression reference and "
                            + "the session's expression table does not "
                            + "hold it");
            return "";
        }
        Term value = dispatch(expression, null, origin + ":" + reference);
        if (value == null) {
            refuse(UNSTATED + ":" + reference,
                    "this expression reference lowers to nothing");
            return "";
        }
        // The JVM evaluated the term, so its Java definedness held where
        // the row was written: it is this conjunction's own fact, exactly
        // as a joined read's observation is.
        sideCondition(value.precondition);
        return value.text;
    }

    /** Whether one symbol occurs in a term as a symbol, not a substring. */
    static boolean mentions(String term, String symbol) {
        if (term == null || symbol == null || symbol.isEmpty()) return false;
        int at = term.indexOf(symbol);
        while (at >= 0) {
            boolean before = at == 0
                    || !symbolCharacter(term.charAt(at - 1));
            int end = at + symbol.length();
            boolean after = end >= term.length()
                    || !symbolCharacter(term.charAt(end));
            if (before && after) return true;
            at = term.indexOf(symbol, at + 1);
        }
        return false;
    }

    /**
     * A character a NAME may be spelled with.
     *
     * <p>SMT-LIB's simple-symbol alphabet, plus the two the runtime's own
     * names use: {@code #} in a row's location symbol, {@code '} in the
     * VM's.  The set was letters, digits, {@code _ . $} -- which splits
     * {@code M_I_field_HOFF.…_edu/uva/liftlab/…} at the slash, so half a
     * name was looked up, no declaration was found for it, and a query
     * emitted a subterm over a constant it never declared.</p>
     */
    private static boolean symbolCharacter(char value) {
        if (Character.isLetterOrDigit(value)) return true;
        return "~!@$%^&*_-+=<>.?/#'".indexOf(value) >= 0;
    }

    /** One lowered expression: its text, its sort, its symbols, or why not. */
    public static final class Lowered {
        private final String text;
        private final String sort;
        private final String refusal;
        private final Map<String, String> declarations;

        private Lowered(String text, String sort, String refusal,
                        Map<String, String> declarations) {
            this.text = text;
            this.sort = sort;
            this.refusal = refusal;
            this.declarations = Collections.unmodifiableMap(declarations);
        }

        private static Lowered refused(String reason) {
            return new Lowered("", "", reason,
                    new LinkedHashMap<String, String>());
        }

        public boolean ok() {
            return refusal.isEmpty() && !text.isEmpty();
        }

        public String text() {
            return text;
        }

        /**
         * The SMT sort this text carries.
         *
         * <p>What a caller binding a variable to this text must DECLARE
         * that variable at -- the composed query declares a joined read at
         * exactly this ({@code Composer.declareStated(read.symbol(),
         * value.sort)}), and a caller that read the sort off the row's Java
         * type instead put an {@code AssocState} chain on the right of a
         * {@code Ref}.</p>
         */
        public String sort() {
            return sort;
        }

        /** Every symbol the text names, with its SMT sort. */
        public Map<String, String> declarations() {
            return declarations;
        }

        @Override
        public String toString() {
            return ok() ? text : "refused:" + refusal;
        }
    }

    // ------------------------------------------------------------------
    // Opening and closing one session's conjunction.
    // ------------------------------------------------------------------

    /**
     * Opens one conjunction, in one session's scope.
     *
     * <p>An execution-local identity is local to the execution that
     * produced it, so two sessions' expressions mentioning one VM symbol
     * are two objects; a name minted without the session in it makes one
     * constant carry both, and a disjunction of satisfiable paths comes
     * back unsat.  The side conditions a lowering raises are likewise true
     * where that execution ran and nowhere else.</p>
     */
    public void begin(String sessionId, SessionJoin sessionJoin) {
        begin(sessionId, sessionJoin, null);
    }

    /**
     * The same, with the session's expression table.
     *
     * <p>The table is what {@link #statedTerm} resolves a published term's
     * expression REFERENCES against, and it is per session for the same
     * reason the join and the identities are: a reference is a name in one
     * recording's table, not a name in the corpus.</p>
     */
    public void begin(String sessionId, SessionJoin sessionJoin,
                      ExpressionTable expressions) {
        // NESTED, not replaced.  One arm of a family is lowered in its own
        // producer's scope in the middle of composing a path, and a begin
        // that overwrote the path's frame left the rest of that path
        // lowered with no write log to join to, no table to resolve a
        // reference against and nowhere to put a refusal -- which is a
        // path admitted on free constants instead of refused by name.
        frames.push(new Frame(openSideConditions, openRefusals, scope, join,
                openTable));
        this.openSideConditions = new ArrayList<String>();
        this.openRefusals = new ArrayList<String>();
        this.scope = sessionId == null ? "" : sessionId;
        this.join = sessionJoin == null ? NO_JOIN : sessionJoin;
        this.openTable = expressions;
    }

    /** Closes it, answering the side conditions its lowering raised. */
    public List<String> end() {
        List<String> conditions = openSideConditions == null
                ? Collections.<String>emptyList() : openSideConditions;
        Frame previous = frames.isEmpty() ? null : frames.pop();
        openSideConditions = previous == null ? null : previous.conditions;
        openRefusals = previous == null ? null : previous.refusals;
        scope = previous == null ? "" : previous.scope;
        join = previous == null ? NO_JOIN : previous.join;
        openTable = previous == null ? null : previous.table;
        return conditions;
    }

    /** One enclosing conjunction, kept while a nested one is open. */
    private static final class Frame {
        private final List<String> conditions;
        private final List<String> refusals;
        private final String scope;
        private final SessionJoin join;
        private final ExpressionTable table;

        private Frame(List<String> conditions, List<String> refusals,
                      String scope, SessionJoin join, ExpressionTable table) {
            this.conditions = conditions;
            this.refusals = refusals;
            this.scope = scope;
            this.join = join;
            this.table = table;
        }
    }

    /** What the conjunction now open refused. */
    public List<String> openRefusals() {
        return openRefusals == null
                ? Collections.<String>emptyList() : openRefusals;
    }

    // ------------------------------------------------------------------
    // What the shared lowering leaves to its caller.
    // ------------------------------------------------------------------

    @Override
    public Term lower(JsonElement expression, Sort expected, String origin) {
        return dispatch(expression, expected, origin);
    }

    @Override
    public Term refuse(VmTermLowering.Reason reason, String origin,
                       String detail, Sort sort) {
        refuse(reason.composedSubject(origin, detail), "");
        return free(sort == null ? Sort.VALUE : sort);
    }

    @Override
    public Term dependent(Term result, Term... inputs) {
        List<String> values = new ArrayList<String>();
        values.add(result.precondition);
        if (inputs != null) {
            for (Term input : inputs) {
                if (input != null) values.add(input.precondition);
            }
        }
        return result.withPrecondition(VmTermLowering.and(values));
    }

    @Override
    public Sort castSort(String descriptor) {
        return JavaSmtSorts.castSort(descriptor);
    }

    @Override
    public Sort sortOfJavaType(String javaType) {
        return JavaSmtSorts.sortOfJava(javaType);
    }

    @Override
    public Term definedResult(String text, Sort sort, IntegralWidth width,
                              String definedness, Term... inputs) {
        return dependent(Term.of(text, sort, width, "", "", definedness),
                inputs);
    }

    @Override
    public Term shortCircuit(String text, Term left, Term right,
                             boolean conjunction) {
        String rightEvaluated = conjunction ? left.text
                : "(not " + left.text + ")";
        return Term.of(text, Sort.BOOL).withPrecondition(
                VmTermLowering.and(Arrays.asList(left.precondition,
                        "(=> " + rightEvaluated + " " + right.precondition
                                + ")")));
    }

    @Override
    public String stringDefinedness(String origin, String operation,
                                    List<Term> dereferenced,
                                    List<Term> evaluated) {
        List<String> values = new ArrayList<String>();
        for (Term value : dereferenced) {
            if (value == null || value.sort != Sort.STRING) {
                values.add("false");
                continue;
            }
            values.add(value.precondition);
            String nullness = value.stringNullness == null
                    || value.stringNullness.isEmpty()
                    ? "true" : value.stringNullness;
            values.add("false".equals(value.stringNullness) ? "true"
                    : "(not " + nullness + ")");
        }
        for (Term value : evaluated) {
            values.add(value == null ? "false" : value.precondition);
        }
        return VmTermLowering.and(values);
    }

    @Override
    public void assertJavaIntegralDomain(String term, Sort sort,
                                         String javaType, String identity) {
        if (sort != Sort.INT || term == null || term.isEmpty()) return;
        JavaPrimitiveSmtSemantics.IntegralDomain domain =
                JavaPrimitiveSmtSemantics.domainOfJavaType(javaType);
        if (domain == null || !integralDomains.add(term)) return;
        assertPlain(VmTermLowering.integralRange(domain.lower, term,
                domain.upper));
    }

    @Override
    public void noteJavaIntToString() {
        usesJavaIntString = true;
    }

    @Override
    public VmTermLowering.RenderedInteger renderedInteger(
            JsonElement element, String origin) {
        return new VmTermLowering.RenderedInteger(null,
                "ROUNDTRIP_NOT_PROVED_NO_SPLIT_EVIDENCE");
    }

    @Override
    public void assertJavaIntRange(Term integer) {
        if (integer == null || integer.sort != Sort.INT) return;
        assertJavaIntegralDomain(integer.text, Sort.INT, "I", integer.text);
    }

    /**
     * What a joined read observed, conjoined into the conjunction open.
     *
     * <p>The joined value is the writer's own expression, which is what
     * makes the chain from a root to this read one formula; the recording
     * also states what the read returned, and that is this execution's own
     * control, exactly as the value it read at a handoff is.  It is
     * conjoined into the path, never asserted globally -- the expression
     * stays free to take other values under other paths' arms.</p>
     */
    @Override
    public void recordedReading(Term value, JsonElement observed,
                                String origin) {
        if (value == null) return;
        Term recorded = dispatch(observed, value.sort,
                origin + ":recorded-reading");
        if (recorded == null || recorded.sort != value.sort) {
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

    @Override
    public Term symbolTerm(JsonObject expression, Sort expected,
                           String origin) {
        String raw = primitiveString(expression, "_exp");
        // Java null, which the VM spells "N" on a SymbolExpression leaf
        // exactly as it does on a constant one (VmExpressionIr
        // .SYMBOLIC_NULL).  Read as a NAME instead, it minted an opaque
        // identity, so "x != null" came out as "x is not this other
        // object" -- satisfiable whatever x is, and silent about nullness,
        // which is what every key case's fatal predicate tests.
        if (VmExpressionIr.SYMBOLIC_NULL.equals(raw)) {
            return nullLeaf(expected);
        }
        if ("V".equals(raw)) return Term.of("true", Sort.BOOL);
        String javaType = primitiveString(expression, "_java_type");
        Sort encoded = JavaSmtSorts.sortOfJava(javaType);
        Sort sort = expected == Sort.MAP || expected == Sort.ARRAY_VALUE
                ? expected
                : encoded != Sort.VALUE ? encoded
                : expected == null ? Sort.REF : expected;
        Declared held = declarations.get(raw);
        if (held != null && held.stated) {
            // The declaration is the mint, the attach, or the read row of
            // this session, and it wins over the shape of the node the
            // symbol turned up in: one variable has one sort.  Whatever
            // bound it -- a root's valuation, an arm, a read's join or its
            // pin -- the leaf is that binding wherever it appears.
            declareStated(raw, held.sort);
            usedSymbols.add(raw);
            return Term.of(raw, held.sort,
                    JavaPrimitiveSmtSemantics.widthOfJavaType(javaType),
                    "", "", "true");
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
                        + "corpus states this symbol", sort);
    }

    /**
     * Java null, at the sort the relation it stands in is written in.
     *
     * <p>A reference is {@code nullRef}; a boxed container cell is the
     * {@code (VRef nullRef)} cell, which is the encoding the container
     * codec already gives a cell that holds null.  A container STATE
     * cannot hold null -- the state IS the contents the VM propagated, and
     * a reference that was null has no state -- so a null compared against
     * one is refused by name rather than folded to a constant by the
     * mixed-sort rule.</p>
     */
    private Term nullLeaf(Sort expected) {
        if (expected == Sort.VALUE) {
            return Term.of(ContainerSmtCodec.NULL_CELL, Sort.VALUE);
        }
        if (expected != null && expected.containerState()) {
            return unstated("NullComparedToContainerState:" + expected,
                    "a container state is the contents this replay "
                            + "propagated, and nothing states whether the "
                            + "reference holding it was null", expected);
        }
        return Term.of("nullRef", Sort.REF);
    }

    @Override
    public Term placeholderTerm(JsonObject expression, String origin) {
        String function = primitiveString(expression, "_place_holder_func");
        int count = optionalInteger(expression, "_count", -1);
        if (!"currentTimeMills".equals(function) || count < 1) {
            refuse("PlaceholderExpression:"
                    + (function.isEmpty() ? "unknown" : function)
                    + "#" + count, "");
            return free(Sort.INT);
        }
        String identity = function + "#" + count;
        String name = symbols.mint("environment__",
                scope + SEPARATOR + identity, 10);
        declare(name, Sort.INT);
        assertJavaIntegralDomain(name, Sort.INT, "J", identity);
        return Term.of(name, Sort.INT, IntegralWidth.JAVA_LONG);
    }

    /**
     * A read, joined to the write version it observed.
     *
     * <p>JOIN, then PIN, then REFUSE -- the one rule for reading state, the
     * same one {@code ContainerSmtCodec.field} states for a projection.
     * Enumerating the versions the VM retained and letting the solver pick
     * one is what made the old composition a reconstruction rather than a
     * merge, so it is not done here at any step.</p>
     *
     * <p>JOIN is the ROW of the write that made the version -- the
     * {@code WriteRow} of this location at this version, in this session --
     * and its two steps are one question asked of the rows:</p>
     * <ol>
     *   <li>a write log entry, whose expression is the writer's own
     *       propagation and whose row also names the writer occurrence the
     *       STATE families are built over;</li>
     *   <li>otherwise the symbol the placeholder row whose
     *       {@code mintVersion} IS this version states.  A mint is not a
     *       write: the VM's primitive gives a declared region input a new
     *       version whose value is the minted symbol, nobody wrote it, and
     *       the row states both halves -- {@code observedVersion}, the
     *       last real write the mint was laid over, which is that row's
     *       OWN join, and {@code mintVersion}, the version a reader
     *       arrives with, which is this one.  Matched by the mint version
     *       and by nothing else: it is unique by construction, where
     *       (occurrence, location) was not, and one occurrence declaring
     *       one cell under two ports made that bridge refuse both
     *       rows.</li>
     * </ol>
     *
     * <p>The node also carries the VM's own expression for the version,
     * under {@code observedVersion} -- the version's value AS THIS READ SAW
     * IT, so for a list read through {@code size()} it is
     * {@code SIZE(state)} where the write log entry is the state.  It is
     * the PROJECTION this execution performed, and it is read only inside
     * step 1, where a row has already stated that a write made the
     * version: rows decide WHETHER and BY WHOM a version was made, and
     * hence what a read may bind to, and this decides which cell of it
     * came back.  Consulted for a version no row states, it binds a read
     * to a value nothing in the recording stands behind -- which is how a
     * symbol the composition never bound reached 18 leaves of the 17960
     * anchor as {@code UndeclaredFreeSymbol} -- and it can hand the formula
     * a value from somewhere other than the writer occurrence the STATE
     * families are keyed by.</p>
     */
    @Override
    public Term guardedReadTerm(JsonObject expression, Sort expected,
                                String origin) {
        JsonObject location = JsonFields.object(expression, "location");
        String key = locationKey(location);
        long version = observedVersion(expression);
        if (!key.isEmpty() && version >= 0L) {
            JsonElement written = join.writeExpression(key, version);
            if (written != null && !written.isJsonNull()) {
                JsonElement projected = observedVersionExpression(expression);
                return observing(element(dispatch(projected != null
                                        && !projected.isJsonNull()
                                        ? projected : written, expected,
                                origin + ":join"), expression, location,
                        key, version, expected, origin), key, version);
            }
            String minted = mintedReadSymbol(join, version);
            if (minted == null) {
                return unstated("MintVersion:" + key + "@" + version + ":"
                                + join.mintedReadSymbols(version),
                        "two placeholder rows of this session state this "
                                + "mint version under different symbols, so "
                                + "what the read it made returned has no "
                                + "answer", expected);
            }
            if (!minted.isEmpty()) {
                return symbolTerm(symbolNode(minted,
                                primitiveString(expression, "_java_type")),
                        expected, origin + ":minted");
            }
        }
        JsonElement concrete = expression.get("concreteValue");
        if (concrete != null && !concrete.isJsonNull()) {
            Term pinned = dispatch(concrete, expected, origin + ":pinned");
            if (pinned != null) return pinned;
        }
        return unstated("Read:" + (key.isEmpty()
                        ? VmRows.sessionLocation(location)
                        : key) + "@" + version,
                "no write of this location at this version in this session, "
                        + "and the recording states no value it returned",
                expected);
    }

    /**
     * The state a NAMED subterm is the value of, kept on the name.
     *
     * <p>The join inlines, so a read of a version the write log covers
     * leaves no trace of the read in the text -- and where the joined value
     * is a container, the text is one {@code container_dag__} name whose
     * body holds the mutation chain and nothing that names the cell.  The
     * read row is what names it, so the row's symbol is recorded ON the
     * subterm the read produced, which is where {@link #reachedSymbols}
     * finds it.  A scalar join is inlined down to the recording's own
     * leaves and names nothing here: this is the one thing a name can hide
     * that a body cannot show.</p>
     *
     * <p>A subterm two reads produce is the SAME closed term, so it is the
     * value of both and carries both rows; nothing is chosen between
     * them.</p>
     */
    private Term observing(Term value, String key, long version) {
        if (value == null) return value;
        SharedTerm shared = sharedByName.get(value.text);
        if (shared != null) {
            shared.states.addAll(join.readSymbols(key, version));
        }
        return value;
    }

    /**
     * One recorded symbol as the VM's own leaf.
     *
     * <p>A symbol a ROW states and a symbol an expression names are the
     * same thing -- the contract makes the two string-equal -- so a row's
     * symbol is lowered by building the leaf the VM would have serialized
     * and asking {@link #symbolTerm} for it.  One leaf rule: the
     * declaration registry decides the sort, an identity spelling mints the
     * same {@code identity__} name every other leaf of that object gets,
     * {@code "N"} is null, and a symbol nothing states is cut by name.</p>
     */
    private static JsonObject symbolNode(String symbol, String javaType) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "SymbolExpression");
        node.addProperty("_exp", symbol);
        node.addProperty("_java_type", javaType == null ? "" : javaType);
        return node;
    }

    /**
     * The term one ROW states as the value its read returned, or null.
     *
     * <p>One implementation for every row that states a value, so that a
     * read row's pin and a {@code FieldAccess} {@code concreteValue} cannot
     * disagree about what a recorded value means.  A reference is the VM's
     * own leaf -- the {@code M_L'class'_rid} identity spelling, or
     * {@code "N"} for null -- through {@link #symbolTerm}, which is where
     * the identity name is minted; a scalar is its literal at the sort the
     * row's Java type names.  A value this places nowhere is null, and the
     * caller names the refusal.</p>
     */
    public Term statedValue(String concreteValue, String javaType,
                            String origin) {
        String text = concreteValue == null ? "" : concreteValue.trim();
        if (text.isEmpty()) return null;
        if (VmExpressionIr.SYMBOLIC_NULL.equals(text)
                || VmRows.referencedObjectRid(text) > 0L) {
            return symbolTerm(symbolNode(text, javaType), null, origin);
        }
        String literal = smtLiteral(text);
        if (literal.isEmpty()) return null;
        Sort sort = JavaSmtSorts.sortOfJava(javaType);
        if (sort != Sort.BOOL && sort != Sort.INT && sort != Sort.FLOAT32
                && sort != Sort.FLOAT64 && sort != Sort.STRING) {
            return null;
        }
        return Term.of(literal, sort,
                JavaPrimitiveSmtSemantics.widthOfJavaType(javaType));
    }

    /**
     * The CELL a read of one element observed, out of a whole-container
     * value the join handed back.
     *
     * <p>A read of one cell can join to a version whose expression is the
     * whole container -- the runtime publishes whatever the writing
     * instruction produced, and for an array store that can be the array
     * state.  The read is of the cell, and the cell's index is the
     * LOCATION's own slot, so the element is
     * {@code indexed_read(state, slot)}: the projection the execution
     * performed, read off the location, not a choice made here.  Handing
     * the state back instead is what put a whole {@code IndexedState} into
     * the index arithmetic of a binary search and refused 1,532 nodes of
     * the 17960 seed as {@code BinarySortConflict:-:ARRAY_VALUE!=INT} --
     * an operator named for a projection that had been thrown away.</p>
     *
     * <p>An associative location names its key by HASH and not by the
     * key's value, so no projection here can state which entry was read:
     * that one is refused by name, naming the location, the version and
     * the two sorts, rather than passed on to collide in an operator.</p>
     */
    private Term element(Term value, JsonObject expression,
                         JsonObject location, String key, long version,
                         Sort expected, String origin) {
        if (value == null || !value.sort.containerState()) return value;
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
            Term unboxed = fromValue(cellValue, javaType, origin);
            if (unboxed != null && !unboxed.sort.containerState()) {
                return dependent(unboxed, value);
            }
        }
        return unstated("ContainerElement:" + (key.isEmpty()
                        ? VmRows.sessionLocation(location) : key)
                        + "@" + version + ":" + value.sort + "!=" + cell,
                "the write this read joined to states the whole container "
                        + "at that version, and this location does not say "
                        + "which cell of it the read returned", cell);
    }

    @Override
    public Term containerTerm(JsonObject expression, boolean field,
                              String origin) {
        ContainerSmtCodec.Term value = field
                ? ContainerSmtCodec.field(expression, host(origin))
                : ContainerSmtCodec.term(expression, host(origin));
        if (value == null) {
            // The codec has already named WHY; this row says WHICH node
            // carried it on.  A field projection states no operation, so
            // naming the operation alone left the row blank -- a refusal
            // nobody can read is the silence rule 8 forbids.
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
            return free(JavaSmtSorts.sortOfJava(
                    primitiveString(expression, "_java_type")));
        }
        Sort sort = VmTermLowering.sortOfContainer(value.sort);
        if (sort == Sort.UNKNOWN) {
            refuse(origin + ":CONTAINER_STATE_USED_AS_VALUE", "");
            return free(Sort.VALUE);
        }
        return Term.vm(value.text, sort, value.integralWidth);
    }

    @Override
    public Term splitElementTerm(JsonObject expression, String origin) {
        refuse("MODEL_SEMANTICS_MISSING:java/lang/String.splitElement", "");
        return free(Sort.STRING);
    }

    @Override
    public Sort methodResultSort(JsonObject expression, String origin) {
        Term result = dispatch(expression.get("_res_exp"), null, origin);
        return result == null ? Sort.VALUE : result.sort;
    }

    // ------------------------------------------------------------------
    // Identities.
    // ------------------------------------------------------------------

    /**
     * One execution-local identity, named once, free but not nothing.
     *
     * <p>Which object an execution ran on says nothing about the failure,
     * so the identity is opaque.  Two things about it were recorded, and
     * stating them is not an assumption: the execution read fields off the
     * object, so it was not null; and two different rids in one session are
     * two different objects.  Left unsaid, a model answers a null check by
     * making the reference null and a lookup by making two keys one object
     * -- which is how 17897's healthy path had both arms satisfiable at its
     * own recorded valuation.</p>
     */
    private String opaque(String raw, Sort sort) {
        String name = symbols.mint("identity__",
                scope + SEPARATOR + sort + SEPARATOR + raw, 10);
        declare(name, sort);
        boolean minted = opaqueIdentities.put(name, raw) == null;
        long rid = VmRows.referencedObjectRid(raw);
        if (minted && sort == Sort.REF && rid > 0L) {
            assertPlain("(not (= " + name + " nullRef))");
            Map<Long, String> held = recordedObjects.get(scope);
            if (held == null) {
                held = new LinkedHashMap<Long, String>();
                recordedObjects.put(scope, held);
            }
            held.put(rid, name);
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

    private ContainerSmtCodec.Host host(final String origin) {
        return new ContainerSmtCodec.Host() {
            @Override
            public ContainerSmtCodec.Term state(
                    JsonElement identity, ContainerSmtCodec.Sort shape) {
                Sort stateSort = shape == ContainerSmtCodec.Sort.INDEXED
                        ? Sort.ARRAY_VALUE : Sort.MAP;
                Term reference = dispatch(identity, Sort.REF,
                        origin + ":container-state");
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
            public boolean preserveContainerIdentity(
                    JsonElement expression, ContainerSmtCodec.Sort expected) {
                return ContainerSmtCodec.evidencedContainerIdentity(
                        expression);
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
                if (ContainerSmtCodec.handles(expression)) {
                    return name(ContainerSmtCodec.term(
                            expression.getAsJsonObject(), this));
                }
                if (ContainerSmtCodec.handlesField(expression)) {
                    return name(ContainerSmtCodec.field(
                            expression.getAsJsonObject(), this));
                }
                Term value = dispatch(expression,
                        VmTermLowering.sortOfContainer(expected),
                        origin + ":container-operand");
                // WITH the Java width it was lowered at: the JVM's shift
                // and bitwise instructions are typed (ISHR is not LSHR),
                // so an operand that arrives through the codec without its
                // width makes the operator over it ambiguous and refuses a
                // projection the recording states exactly -- 14 of the
                // 17960 seed's expressions, as
                // AmbiguousJavaIntegralShift:>>:NONE:JAVA_INT.
                return value == null ? null : new ContainerSmtCodec.Term(
                        value.text,
                        VmTermLowering.containerSortOf(value.sort),
                        value.integralWidth);
            }

            @Override
            public ContainerSmtCodec.Term box(JsonElement expression) {
                Term value = dispatch(expression, null,
                        origin + ":container-value");
                if (value == null) return null;
                String javaType =
                        VmTermLowering.expressionJavaType(expression);
                String boxed = boxed(value, javaType);
                if (boxed.isEmpty()) {
                    // Name what could not be boxed: "CannotBox:L" alone
                    // says the declared type and not the shape the value
                    // came out as, which is the half that decides whether
                    // the cell or the lowering of it is wrong.
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
                return name(ContainerSmtCodec.unboxValue(value, javaType,
                        VmTermLowering.unboxedCellSort(
                                JavaSmtSorts.sortOfJava(javaType)), this));
            }

            @Override
            public void require(String predicate) {
                sideCondition(predicate);
            }

            @Override
            public void unsupported(String reason) {
                refuse(reason, "");
            }
        };
    }

    private static String boxed(Term value, String javaType) {
        String integral = ContainerSmtCodec.boxIntegral(value.text, javaType);
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
        /**
         * The recorded STATE this subterm is the value of: the symbols the
         * read rows of the version it was lowered from state.
         *
         * <p>Not in the body and not derivable from it.  A container
         * version is the chain of the mutations that built it, and the
         * chain's own base is an empty container as often as it is a
         * symbol -- 11741's {@code allKeys} is six {@code PUT}s over a
         * {@code SNAPSHOT_BASE} -- so the body names the values that were
         * put in and nothing that names the CELL they were put in.  The
         * read that produced the subterm is what names it, and this is
         * where that row's symbol is kept, so that a term reaching the
         * subterm reaches the state the recording read.</p>
         */
        private final Set<String> states = new LinkedHashSet<String>();

        private SharedTerm(String name, Sort sort, String body) {
            this.name = name;
            this.sort = sort;
            this.body = body;
        }
    }

    /**
     * Names a pure container subterm, or returns it unchanged.
     *
     * <p>A container version is read by every condition that mentions it,
     * and its chain is the whole mutation history; re-inlining it at each
     * read grows the formula as the product of the two.  Naming it costs
     * one define-fun and changes nothing the formula means.</p>
     */
    private ContainerSmtCodec.Term name(ContainerSmtCodec.Term value) {
        if (value == null || value.text.isEmpty()
                || value.text.charAt(0) != '(') {
            return value;
        }
        Sort sort = VmTermLowering.sortOfContainer(value.sort);
        if (sort == Sort.UNKNOWN) return value;
        // The digest is over the SCOPED text: a subterm that mentions a
        // recorded symbol is one session's term, because the symbol is that
        // session's row, and two sessions share a name only when the
        // definition is literally the same closed term.  An identity and an
        // environment cell already carry the scope in their own mint; this
        // is the same rule for the one name that did not.
        String identity = sort.name() + SEPARATOR + scoped(value.text);
        String digest = ArtifactIO.digest(identity, 0);
        SharedTerm held = sharedTerms.get(digest);
        if (held == null) {
            held = new SharedTerm(symbols.mint("container_dag__", identity,
                    24), sort, value.text);
            sharedTerms.put(digest, held);
            sharedByName.put(held.name, held);
        }
        return new ContainerSmtCodec.Term(held.name, value.sort,
                value.integralWidth, value.indexedSize);
    }

    // ------------------------------------------------------------------
    // The query.
    // ------------------------------------------------------------------

    /**
     * One term's text with every RECORDED symbol in it read as this
     * session's.
     *
     * <p>For the digest only: what is emitted is the text as it stands.  A
     * recorded symbol is a row of one recording, so the same spelling in
     * two sessions is two values, and a name minted over the bare text
     * would make one definition of the two.</p>
     */
    private String scoped(String text) {
        if (text == null || text.isEmpty() || scope.isEmpty()) return text;
        StringBuilder out = new StringBuilder(text.length());
        int index = 0;
        while (index < text.length()) {
            char value = text.charAt(index);
            if (!symbolCharacter(value)) {
                out.append(value);
                index++;
                continue;
            }
            int end = index;
            while (end < text.length()
                    && symbolCharacter(text.charAt(end))) {
                end++;
            }
            String token = text.substring(index, end);
            index = end;
            if (usedSymbols.contains(token)) {
                out.append(scope).append(SEPARATOR);
            }
            out.append(token);
        }
        return out.toString();
    }

    /**
     * Declares one name THIS LOWERING minted; a second, different sort is
     * a defect.
     */
    public void declare(String name, Sort sort) {
        put(name, sort, false);
    }

    /**
     * Declares one name a ROW of the recording states, at the sort the
     * row's own binding gives it.
     *
     * <p>Same registry, same sort rule; what it adds is the authority. A
     * leaf naming this symbol now lowers to it -- to the binding the path
     * states for it -- instead of being cut as a free symbol.</p>
     */
    public void declareStated(String name, Sort sort) {
        put(name, sort, true);
    }

    /**
     * Puts a name the recording already states into the query, answering
     * whether the recording states one.
     *
     * <p>For a caller holding a term's text rather than its leaves: a
     * published term can name a recorded symbol directly, and the
     * registry is the one place that says whether the recording declares
     * it and at what sort.</p>
     */
    public boolean declareStated(String name) {
        Declared held = declarations.get(name);
        if (held == null || !held.stated) return false;
        put(name, held.sort, true);
        return true;
    }

    /**
     * One name, one sort -- and a second sort is a named refusal.
     *
     * <p>It used to throw, and a composer that dies on its input has told
     * the reader nothing: the first three-session 17960 corpus reached it
     * because two of its sessions published an EMPTY expression table
     * while their rows cited 28 refs each, so one session bound a read
     * row's symbol at {@code Int} and another bound the same symbol at the
     * sort an ABSENT expression refuses at.  What two rows say about one
     * symbol is something the CORPUS states, so it is refused by name --
     * which drops the path being lowered -- and kept for the caller to
     * raise as a BLOCKING gap, so the composition closes fail-closed
     * instead of by a stack trace.</p>
     *
     * <p>The FIRST declaration stands.  A name already written into an
     * assertion at one sort cannot be re-sorted under it without making
     * that assertion ill-sorted, which z3 answers with {@code (error …)} --
     * and no {@code (error …)} is ever acceptable.</p>
     */
    private void put(String name, Sort sort, boolean stated) {
        Declared held = declarations.get(name);
        if (held != null && held.sort != sort) {
            String detail = held.sort + " and " + sort;
            sortConflicts.put(name, detail);
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
        return Collections.unmodifiableMap(sortConflicts);
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
     * Whether this query gives one name a meaning at all.
     *
     * <p>Two ways it can: a {@code declare-const}, or a {@code define-fun}
     * for a named container subterm.  A caller asking "is this term over
     * things the query states" means both -- a shared term is a definition,
     * which is more than a declaration, not less.</p>
     */
    public boolean defined(String name) {
        return declared(name) || sharedByName.containsKey(name);
    }

    /** The names this query declares, at the sorts it declares them. */
    public Map<String, Sort> declarations() {
        Map<String, Sort> named = new LinkedHashMap<String, Sort>();
        for (Map.Entry<String, Declared> entry
                : declarations.entrySet()) {
            if (entry.getValue().inQuery) {
                named.put(entry.getKey(), entry.getValue().sort);
            }
        }
        return Collections.unmodifiableMap(named);
    }

    /**
     * Whether THIS LOWERING invented the name, rather than the recording.
     *
     * <p>Two kinds of name reach a lowered term and they are not the same
     * fact.  A name the lowering minted -- a container subterm, an
     * execution-local identity, an environment cell -- means exactly what
     * the query says it means, because the query defines it.  A name that
     * came off a {@code SymbolExpression} leaf means whatever the RECORDING
     * says it means, and if no mint, attach or read declares it, nothing
     * says: a caller must refuse it by name rather than declare it free.
     * The second kind is {@link #usedSymbols}; this is the first.</p>
     */
    public boolean minted(String name) {
        return defined(name) && !usedSymbols.contains(name);
    }

    /**
     * Every name the fixed preamble gives a meaning to.
     *
     * <p>Sorts, datatype constructors and selectors, and the functions the
     * container model is written in.  A caller that renders the preamble
     * states these; one that reads a lowered term must not call them free.
     * Read off the preamble text so the two cannot drift apart.</p>
     */
    public static Set<String> preambleNames() {
        if (PREAMBLE_NAMES.isEmpty()) {
            List<String> lines = new ArrayList<String>(
                    VmTermLowering.preamble(false));
            lines.add(VmTermLowering.JAVA_INT_TO_STRING);
            lines.add(JavaPrimitiveSmtSemantics.INT_WRAP_DEFINITION);
            lines.add(JavaPrimitiveSmtSemantics.LONG_WRAP_DEFINITION);
            for (String line : lines) {
                for (String name : declaredIn(line)) PREAMBLE_NAMES.add(name);
            }
        }
        return PREAMBLE_NAMES;
    }

    private static final Set<String> PREAMBLE_NAMES =
            new LinkedHashSet<String>();

    /** The names one preamble line states: the head of every list in it. */
    private static List<String> declaredIn(String line) {
        List<String> names = new ArrayList<String>();
        if (line == null) return names;
        boolean datatype = line.startsWith("(declare-datatypes");
        for (int index = 0; index < line.length(); index++) {
            if (line.charAt(index) != '(') continue;
            int end = index + 1;
            while (end < line.length()
                    && symbolCharacter(line.charAt(end))) end++;
            String head = line.substring(index + 1, end);
            if (head.isEmpty()) continue;
            // Outside a datatype only a declaration states a name, and it is
            // the token after the keyword; inside one, every list opens with
            // a sort, a constructor or a selector.
            if (datatype) {
                names.add(head);
                continue;
            }
            if (!head.startsWith("declare-") && !head.startsWith("define-")) {
                continue;
            }
            int from = end;
            while (from < line.length()
                    && Character.isWhitespace(line.charAt(from))) {
                from++;
            }
            int to = from;
            while (to < line.length()
                    && symbolCharacter(line.charAt(to))) to++;
            if (to > from) names.add(line.substring(from, to));
        }
        return names;
    }

    /** Lowers one value expression, keeping its sort. */
    public Term term(JsonElement expression, Sort expected, String origin) {
        return dispatch(expression, expected, origin);
    }

    private void sideCondition(String predicate) {
        if (predicate == null || predicate.isEmpty()
                || "true".equals(predicate)) {
            return;
        }
        if (openSideConditions != null) {
            if (!openSideConditions.contains(predicate)) {
                openSideConditions.add(predicate);
            }
        } else {
            assertPlain(predicate);
        }
    }

    private void refuse(String subject, String detail) {
        unsupported.add(subject);
        if (openRefusals != null) openRefusals.add(subject);
        if (detail != null && !detail.isEmpty()) {
            unsupportedDetail.put(subject, detail);
        }
    }

    private Term cut(String subject, String detail, Sort sort) {
        cuts.add(subject);
        refuse(CUT + ":" + subject, detail);
        return free(sort == null ? Sort.VALUE : sort);
    }

    private Term unstated(String subject, String detail, Sort sort) {
        refuse(UNSTATED + ":" + subject, detail);
        return free(sort == null ? Sort.VALUE : sort);
    }

    /** One fresh unconstrained value, for a construct this refused. */
    private Term free(Sort sort) {
        Sort declared = sort == null || sort == Sort.UNKNOWN
                ? Sort.VALUE : sort;
        String name = symbols.mint("unsupported__",
                scope + "#" + declared + "#" + unsupported.size(), 10);
        declare(name, declared);
        return Term.of(name, declared, declared == Sort.INT
                ? IntegralWidth.JAVA_INT : IntegralWidth.NONE);
    }

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
     * What this lowering states about the names one caller's texts reach.
     *
     * <p>THE FACTS.  A lowering does not only name the values a term is
     * written over, it also states what the recording establishes about
     * them, and those statements are as much part of the question as the
     * term: an {@code identity__} is a reference the execution read fields
     * off, so {@link #opaque} states it was not null, and a query that
     * emits the name without the fact has freed a boundary CLOSURE-V2 SS3
     * forbids freeing.  That is how 18 of hdfs-11741's 36 wave-0 flip
     * queries -- {@code (= container_dag__... nullRef)}, negated -- were
     * satisfied: by making the object the recording saw null, with no
     * variable declared at all ({@code (get-value ())}).</p>
     *
     * <p>The composed query emits them with the body ({@link #body}); a
     * query a caller assembles itself has to ask, and it asks for exactly
     * the facts its own text reaches, for the reason {@link #reachedBy}
     * declares exactly what its text reaches.  EVERY name of a fact must be
     * one of those, not merely one: a fact is a relation between names, and
     * half of one is not a weaker fact but a different one -- and stating
     * it would put a name in the query that nothing there binds.</p>
     */
    public List<String> facts(Iterable<String> texts) {
        Set<String> reached = new LinkedHashSet<String>(preambleNames());
        for (Declaration declaration : reachedBy(texts)) {
            reached.add(declaration.name);
        }
        List<String> stated = new ArrayList<String>();
        for (Stated held : assertions) {
            if (!held.label.isEmpty()) continue;
            boolean whole = true;
            for (String name : names(held.formula)) {
                if (BUILTIN.contains(name) || reached.contains(name)) {
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

    public Map<String, String> unsupportedDetail() {
        return unsupportedDetail;
    }

    public Set<String> cuts() {
        return cuts;
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
     * Exactly the declarations these texts reach, dependencies first.
     *
     * <p>A query that emitted every declaration its lowering ever made
     * would state symbols from terms it does not conjoin -- a lowering is
     * cached per session and answers many questions -- and a reader cannot
     * tell those from the ones the query rests on.  Reachability is by the
     * names a text mentions, through the bodies of the subterms it names,
     * to a fixed point.</p>
     */
    public List<Declaration> reachedBy(Iterable<String> texts) {
        List<Declaration> ordered = new ArrayList<Declaration>();
        Set<String> done = new LinkedHashSet<String>();
        if (texts != null) {
            for (String text : texts) {
                reach(text, done, ordered, 0);
            }
        }
        return ordered;
    }

    private void reach(String text, Set<String> done,
                       List<Declaration> ordered, int depth) {
        if (text == null || text.isEmpty() || depth > 512) return;
        for (String token : names(text)) {
            if (!done.add(token)) continue;
            SharedTerm shared = sharedByName.get(token);
            if (shared != null) {
                // Its own dependencies first: a define-fun may name another.
                reach(shared.body, done, ordered, depth + 1);
                ordered.add(new Declaration(shared.name, shared.sort.smt,
                        shared.body));
                continue;
            }
            Declared held = declarations.get(token);
            if (held != null && held.inQuery) {
                ordered.add(new Declaration(token, held.sort.smt, ""));
            }
        }
    }

    /**
     * Every name the query's own logic gives a meaning to.
     *
     * <p>The operators belong here for the same reason the datatype
     * selectors do: in SMT-LIB {@code =} and {@code <=} are SYMBOLS, and
     * {@link #names} reads them as such, so a caller asking "which names
     * does nothing declare" must be told that the theory declares these.
     * Left out, the check reported {@code =} as a free symbol of every term
     * it read.</p>
     *
     * <p>One set, for both stages: it was the composer's private BUILTIN and
     * the flip query's own KEYWORDS, and the two differed -- the flip
     * query's was missing every datatype selector and every bit-vector
     * operator the composer lists, and the composer's was missing
     * {@code is_int} beside the {@code to_int} and {@code to_real} it
     * already had.  Two vocabularies over one query text is a name one
     * stage calls a theory operator and the other calls undeclared.</p>
     */
    public static final Set<String> BUILTIN =
            Collections.unmodifiableSet(new LinkedHashSet<String>(
                    Arrays.asList("=", "=>", "+", "-", "*", "/", "<", "<=",
                    ">", ">=", "!", "_",
                    "and", "or", "not", "xor", "ite", "let", "forall",
                    "exists", "distinct", "true", "false", "div", "mod",
                    "abs", "rem", "select", "store", "as", "const", "lambda",
                    "is", "bvadd", "bvsub", "bvmul", "bvand", "bvor",
                    "bvxor", "bvnot", "bvshl", "bvlshr", "bvashr", "bvsdiv",
                    "bvudiv", "bvsrem", "bvurem", "bvule", "bvult", "bvsle",
                    "bvslt", "bvuge", "bvugt", "bvsge", "bvsgt", "concat",
                    "extract", "zero_extend", "sign_extend", "Int", "Bool",
                    "Real", "String", "Ref", "Value", "AssocState",
                    "IndexedState", "FloatingPoint", "RoundingMode",
                    "roundNearestTiesToEven", "RNE", "RTZ", "RTP", "RTN",
                    "RNA", "nullRef", "java_int_wrap", "java_long_wrap",
                    "java_int_to_string", "indexed_state_of",
                    "assoc_state_of", "indexed_read", "indexed_write",
                    "indexed_append", "indexed_insert", "indexed_remove",
                    "indexed_contains", "indexed_size", "indexed_elements",
                    "assoc_has", "assoc_read", "assoc_key_at",
                    "assoc_value_at", "assoc_put", "assoc_remove",
                    "assoc_size", "assoc_present", "assoc_values",
                    "assoc_order", "assoc_position", "VByte", "VChar",
                    "VShort", "VInt", "VLong", "VFloat", "VDouble", "VBool",
                    "VRef", "VString", "valueByte", "valueChar", "valueShort",
                    "valueInt", "valueLong", "valueFloat", "valueDouble",
                    "valueBool", "valueRef", "valueString", "str", "fp",
                    "to_real", "to_int", "is_int", "divisible")));

    /**
     * Every NAME one SMT term names: the one tokenizer.
     *
     * <p>The alphabet is {@link #symbolCharacter}'s, which is SMT-LIB's, so
     * {@code /} and {@code #} are parts of a name and not breaks in it.  A
     * second tokenizer that stopped at {@code /} cut
     * {@code M_I_field_REGION...._java/util/concurrent/atomic/AtomicInteger}
     * into five pieces and reported all five as symbols nothing declares --
     * the same one-rule-two-implementations defect as the two declaration
     * maps, in the same path.  Text inside {@code "..."} is a literal and
     * names nothing; text inside {@code |...|} is ONE name, however it is
     * spelled; a numeral is a value and not a name, and neither is a
     * {@code #x}/{@code #b} literal.</p>
     */
    public static List<String> names(String text) {
        List<String> names = new ArrayList<String>();
        pass(text, Collections.<String, String>emptyMap(), names);
        return names;
    }

    /**
     * The symbols of one term, THROUGH the container subterms it names.
     *
     * <p>{@link #symbols} reads the text as it stands, and a container
     * version does not stand there: {@link #name} replaces a pure container
     * subterm with a {@code container_dag__} name and keeps the body for a
     * {@code define-fun}, so a guard over a map read lowers to
     * {@code (not (= container_dag__6a41cea2ab3d97c2e6bebb3c nullRef))} --
     * one name, and it declares nothing.  A caller asking the CORPUS about
     * the symbols of a term means the recording's own names, and every one
     * of them is inside that body.  11741's anchor guard
     * {@code allKeys.get(keyId) == null} is exactly this shape, and the
     * closure planner, asking {@link #symbols}, matched no read row and no
     * attach row of the anchor: its whole closure was the anchor's own
     * state-connected group on one node, so no NameNode occurrence was ever
     * demanded and wave 0 had one guard to flip.</p>
     *
     * <p>The same reachability {@link #reachedBy} emits declarations with --
     * the names a text mentions, through the bodies of the subterms it
     * names, to a fixed point -- and a name this lowering MINTED is not one
     * of the recording's, so it is walked through and never reported.</p>
     *
     * <p>TWO FACTS about one term, and one walk that tells them apart.
     * {@code into} is what the term SAYS: the recording's names, reachable
     * through the bodies of the subterms it names.  {@code states} is what
     * the term RESTS ON and does not say: the read row behind a named
     * container subterm, the version it is the value of
     * ({@link SharedTerm#states}), which the join inlined.  The closure
     * planner passes one set for both -- it is asking what the failure can
     * DEPEND on.  The flip query keeps them apart and binds each by its own
     * rule: a name the text says is a variable of the query, and the state
     * behind the name is the v_C variable, joined to its writers.  Passing
     * one set there declared a variable of the container sort for a map the
     * query does not name, which took 11741's anchor obligation from
     * {@code SAT_MODEL_READY} to a refusal on that sort.  There is no
     * two-argument form: a caller that does not want the states says so by
     * handing an empty set it then ignores, and the one that had it bound
     * no container state at all.</p>
     */
    public Set<String> reachedSymbols(String text, Set<String> into,
                                      Set<String> states) {
        reachedSymbols(text, new LinkedHashSet<String>(), into, states, 0);
        return into;
    }

    private void reachedSymbols(String text, Set<String> seen,
                                Set<String> into, Set<String> states,
                                int depth) {
        if (text == null || text.isEmpty() || depth > 512) return;
        for (String name : names(text)) {
            if (BUILTIN.contains(name) || !seen.add(name)) continue;
            SharedTerm shared = sharedByName.get(name);
            if (shared != null) {
                // A container subterm is the value of a recorded STATE, and
                // that state is the subterm's own fact and not a name in its
                // body: the chain the dag holds is the mutations, whose base
                // is as often the empty container as a symbol.  11741's
                // anchor guard is exactly that -- six PUTs over a
                // SNAPSHOT_BASE -- so the body named the five handoffs that
                // were put in and nothing that named the cell, the anchor's
                // own read row was ADMISSION_GAP, writers() was never asked
                // for it, and no NameNode occurrence could enter the
                // closure.  The v_C rule (CLOSURE-V2): a term that reaches
                // the dag rests on the state the dag stands for.
                if (states != null) states.addAll(shared.states);
                reachedSymbols(shared.body, seen, into, states, depth + 1);
                continue;
            }
            // A name this lowering MINTED means what the query says it
            // means and the corpus has never heard of it; a name off a
            // recorded leaf means whatever the RECORDING says
            // ({@link #minted}).  Only the second kind is a symbol a
            // caller can ask the corpus about.
            if (minted(name)) continue;
            into.add(name);
        }
    }

    /**
     * The same names, minus the ones the theory declares.
     *
     * <p>What a caller means by "the symbols of this term": the free names,
     * which it then asks the corpus about.  One tokenizer, one vocabulary --
     * the flip query and the closure planner each had their own pair.</p>
     */
    public static Set<String> symbols(String text, Set<String> into) {
        for (String name : names(text)) {
            if (!BUILTIN.contains(name)) into.add(name);
        }
        return into;
    }

    /**
     * The same text with the caller's renames applied, and every name it
     * left free that nothing states.
     *
     * <p>A recorded predicate arrives already spelled in SMT-LIB over the
     * symbols the recording declared, so a stage that needs it over its own
     * variables RENAMES -- it never re-derives the predicate.  Renaming is
     * therefore one pass of the one tokenizer, and a token the renames do
     * not name is copied through exactly as it was written, bars and all.</p>
     *
     * <p>{@code unknown} collects the free names that are neither theory
     * vocabulary nor stated by {@code stated}; that is what makes a query
     * refuse itself rather than emit a formula over a constant nothing
     * declares.  A term that BINDS names of its own ({@code let}) reports
     * none of them, because a bound name is not free and the pass does not
     * track scopes.</p>
     */
    public static String rename(String text, Map<String, String> renames,
                                Predicate<String> stated,
                                Set<String> unknown) {
        Set<String> named = new LinkedHashSet<String>();
        String out = pass(text, renames, named);
        if (text != null && !text.contains("(let ")) {
            for (String name : named) {
                if (BUILTIN.contains(name)) continue;
                if (stated != null && stated.test(name)) continue;
                unknown.add(name);
            }
        }
        return out.trim();
    }

    /**
     * ONE pass over an SMT term: the names it names, renamed where asked.
     *
     * <p>Every consumer of a term's names goes through here -- "which names
     * are these", "which of them is free", "the same term over my own
     * variables" -- so the three questions are asked of one tokenizer and
     * cannot disagree about where a name ends.</p>
     */
    /** How the one tokenizer spells the names it copies through. */
    private enum Spelling {
        /** Exactly as written, which is what a rename pass needs. */
        AS_WRITTEN,
        /**
         * Bar-quoted where SMT-LIB cannot spell the name bare.
         *
         * <p>A row's symbol is a NAME the runtime chose --
         * {@code MAP_STATE/4#-3@v112} -- and {@code #} is not in SMT-LIB's
         * simple-symbol alphabet: it opens a bit-vector literal, so z3
         * answers the whole query with "invalid bit-vector literal" and the
         * composition has no verdict at all.  {@code |...|} is the SAME
         * symbol spelled legally, which is why the fix is a spelling and
         * not a rename: renaming would need every published term rewritten
         * in step, and a term the runtime wrote about {@code x} must stay
         * about {@code x}.  Idempotent, because an already-quoted name is
         * one token here and is copied through.</p>
         */
        LEGAL
    }

    private static String pass(String text, Map<String, String> renames,
                               Collection<String> named) {
        return pass(text, renames, named, Spelling.AS_WRITTEN);
    }

    private static String pass(String text, Map<String, String> renames,
                               Collection<String> named, Spelling spelling) {
        StringBuilder out = new StringBuilder();
        if (text == null) return "";
        int index = 0;
        while (index < text.length()) {
            char value = text.charAt(index);
            if (value == '"') {
                int end = pastLiteral(text, index, '"');
                out.append(text, index, end);
                index = end;
                continue;
            }
            if (value == ';') {
                // A comment runs to the end of the line and names nothing.
                int end = text.indexOf('\n', index);
                end = end < 0 ? text.length() : end;
                out.append(text, index, end);
                index = end;
                continue;
            }
            if (value == '|') {
                int end = pastLiteral(text, index, '|');
                String token = text.substring(index + 1,
                        Math.max(index + 1, end - 1));
                index = emit(out, text, index, end, token, renames, named,
                        Spelling.AS_WRITTEN);
                continue;
            }
            if (!symbolCharacter(value)) {
                out.append(value);
                index++;
                continue;
            }
            int end = index;
            while (end < text.length()
                    && symbolCharacter(text.charAt(end))) {
                end++;
            }
            index = emit(out, text, index, end, text.substring(index, end),
                    renames, named, spelling);
        }
        return out.toString();
    }

    /**
     * One token: renamed, or copied exactly as it was spelled.
     *
     * @return the index past the token
     */
    private static int emit(StringBuilder out, String text, int start,
                            int end, String token,
                            Map<String, String> renames,
                            Collection<String> named, Spelling spelling) {
        if (!name(token)) {
            append(out, text, start, end, token, spelling);
            return end;
        }
        String renamed = renames.get(token);
        if (renamed != null) {
            out.append(renamed);
            return end;
        }
        append(out, text, start, end, token, spelling);
        named.add(token);
        return end;
    }

    private static void append(StringBuilder out, String text, int start,
                               int end, String token, Spelling spelling) {
        if (spelling == Spelling.LEGAL && !simpleSymbol(token)) {
            out.append('|').append(token).append('|');
            return;
        }
        out.append(text, start, end);
    }

    /** One index past the literal that opens at {@code at}. */
    private static int pastLiteral(String text, int at, char delimiter) {
        int index = at + 1;
        while (index < text.length() && text.charAt(index) != delimiter) {
            index++;
        }
        return index < text.length() ? index + 1 : index;
    }

    /**
     * Whether one token is a NAME and not a value.
     *
     * <p>A numeral is a value; so is {@code #x1f} and {@code #b01}, which
     * SMT-LIB spells with a {@code #} that {@link #symbolCharacter} admits
     * because the runtime's own location symbols use one.  Reporting a
     * hexadecimal literal as a free name is how a float in a lowered term
     * became "this term names symbols nothing declares".</p>
     */
    private static boolean name(String token) {
        if (token.isEmpty()) return false;
        char first = token.charAt(0);
        return !Character.isDigit(first) && first != '-' && first != '.'
                && first != '#';
    }

    /** The preamble alone: the sorts and functions, no declaration. */
    public List<String> preambleLines() {
        List<String> lines = new ArrayList<String>();
        lines.add("(set-logic ALL)");
        lines.add("(set-option :produce-models true)");
        for (String line : VmTermLowering.preamble(false)) lines.add(line);
        if (usesJavaIntString) {
            lines.add(VmTermLowering.JAVA_INT_TO_STRING);
        }
        lines.add(JavaPrimitiveSmtSemantics.INT_WRAP_DEFINITION);
        lines.add(JavaPrimitiveSmtSemantics.LONG_WRAP_DEFINITION);
        return lines;
    }

    private void appendPreamble(StringBuilder query) {
        query.append("; GraphChecker composed query").append('\n');
        // Before the logic and before every assertion: z3 accepts :named
        // annotations without it, but (get-unsat-core) then errors, and a
        // core naming the conjuncts is the whole point of naming them.
        query.append("(set-option :produce-unsat-cores true)").append('\n');
        query.append("(set-logic ALL)").append('\n');
        query.append("(set-option :produce-models true)").append('\n');
        for (String line : VmTermLowering.preamble(false)) {
            query.append(line).append('\n');
        }
        if (usesJavaIntString) {
            query.append(VmTermLowering.JAVA_INT_TO_STRING).append('\n');
        }
        query.append(JavaPrimitiveSmtSemantics.INT_WRAP_DEFINITION)
                .append('\n');
        query.append(JavaPrimitiveSmtSemantics.LONG_WRAP_DEFINITION)
                .append('\n');
    }

    /** The query body: preamble, declarations, assertions; no check-sat. */
    public String body() {
        return body(Collections.<String>emptyList());
    }

    /**
     * The same body, declaring what {@code alsoAsked} reaches as well.
     *
     * <p>ONLY WHAT AN ASSERTION MENTIONS is declared.  A lowering is cached
     * per session and answers many questions, and a term it lowered for a
     * question the composition then DROPPED still left its names in the
     * declaration table: hdfs-17960's candidate.smt2 declared
     * {@code unsupported__d8d8220dc6}, {@code INSTANCE_FIELD/17#60@v209} and
     * {@code path_selector__0__f65d8f3a19} -- the placeholder for a cut
     * value, a read of the cut session, and the selector of the path that was
     * cut -- and used none of them.  A reader cannot tell those from the
     * names the query rests on, which is the whole point of declaring them.
     * {@link #reachedBy} is the one implementation of "what this text
     * reaches", dependencies first, and the flip query already used it.</p>
     *
     * <p>{@code alsoAsked} is the text of the questions this body will be
     * ASKED with but does not contain -- the valuation pins, which name a
     * declared root the body's own assertions need not mention.  They are
     * reached for declaration and not appended: {@link Composition#query}
     * appends the one valuation it is asking about.</p>
     */
    public String body(Iterable<String> alsoAsked) {
        StringBuilder query = new StringBuilder();
        appendPreamble(query);
        List<String> texts = new ArrayList<String>();
        for (Stated held : assertions) texts.add(held.formula);
        if (alsoAsked != null) {
            for (String text : alsoAsked) {
                if (text != null && !text.isEmpty()) texts.add(text);
            }
        }
        for (Declaration declaration : reachedBy(texts)) {
            query.append(declaration.render()).append('\n');
        }
        for (Stated held : assertions) {
            query.append(held.render()).append('\n');
        }
        return legalSymbols(query.toString());
    }

    /**
     * The same text, with every name SMT-LIB cannot spell bare quoted.
     *
     * <p>A row's symbol is a NAME the runtime chose --
     * {@code MAP_STATE/4#-3@v112} -- and {@code #} is not in SMT-LIB's
     * simple-symbol alphabet: it opens a bit-vector literal, so z3 answers
     * the whole query with "invalid bit-vector literal" and the
     * composition has no verdict at all.  {@code |...|} is the SAME symbol
     * spelled legally, which is why the fix is a spelling and not a
     * rename: renaming would need every published term rewritten in step,
     * and a term the runtime wrote about {@code x} must stay about
     * {@code x}.</p>
     *
     * <p>Idempotent: an already-quoted name is copied through, so a body
     * that passes here twice is the text it was.</p>
     */
    public static String legalSymbols(String query) {
        if (query == null || query.isEmpty()) return query;
        return pass(query, Collections.<String, String>emptyMap(),
                new ArrayList<String>(), Spelling.LEGAL);
    }

    /** Copies one string or one already-quoted symbol, closing mark and
     *  all. */
    /** Whether SMT-LIB already spells this token the way it is written. */
    private static boolean simpleSymbol(String token) {
        if (token.isEmpty()) return true;
        char first = token.charAt(0);
        // A keyword, a numeral or a radix literal is not a symbol at all.
        if (first == ':' || first == '#' || Character.isDigit(first)) {
            return true;
        }
        for (int index = 0; index < token.length(); index++) {
            if (!simpleCharacter(token.charAt(index))) return false;
        }
        return true;
    }

    private static boolean simpleCharacter(char value) {
        if (Character.isLetterOrDigit(value)) return true;
        return "~!@$%^&*_-+=<>.?/".indexOf(value) >= 0;
    }

    /** The whole query, at the assertions it holds. */
    public String render() {
        return body() + "(check-sat)\n";
    }

    // ------------------------------------------------------------------
    // Reading a recorded location out of a VM node.
    // ------------------------------------------------------------------

    /**
     * The join key of one recorded location.
     *
     * <p>One spelling for the two authorities on a location: the write log
     * the runtime publishes as {@code WriteRow.location()}, and the location
     * node a VM expression carries inside itself.  A key that differed
     * between them would silently make every state join miss.</p>
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
        JsonElement observed = node.get(VmRows.OBSERVED_VERSION);
        if (observed == null || !observed.isJsonObject()) return null;
        return observed.getAsJsonObject().get("expression");
    }

    private static long observedVersion(JsonObject node) {
        JsonElement observed = node.get(
                VmRows.OBSERVED_VERSION);
        if (observed == null || observed.isJsonNull()) return -1L;
        if (observed.isJsonObject()) {
            return optionalLongInteger(observed.getAsJsonObject(),
                    "fieldVersionId", -1L);
        }
        try {
            return observed.getAsLong();
        } catch (RuntimeException notANumber) {
            return -1L;
        }
    }

    /** What separates the parts of a minted name's identity. */
    private static final String SEPARATOR = "|";
}
