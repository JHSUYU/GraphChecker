package edu.uva.liftlab.graphchecker.d3.compose;

import edu.uva.liftlab.graphchecker.d3.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.d3.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.d3.smt.VmRows;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.d3.smt.JavaPrimitiveSmtSemantics.IntegralWidth;
import edu.uva.liftlab.graphchecker.d3.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.d3.compose.VmTermLowering.Term;
import edu.uva.liftlab.graphchecker.d3.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.d3.contract.LocationId;
import edu.uva.liftlab.graphchecker.d3.contract.LocationKind;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.SessionReader;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The ONE SMT lowering of Design 3: the composer's and the flip solver's.
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
         * The symbols the ROWS in this view state for a read of this
         * location.
         *
         * <p>A version no write log entry covers can still be a read the
         * recording states.  The VM's mint primitive gives a declared
         * region input a fresh version whose value IS the minted symbol,
         * so nobody wrote it and the row contract publishes it as a READ:
         * the reading occurrence's own statement of what that read
         * returned -- the location, the symbol and the plain decimal.  The
         * row states a version too, but it is the version the mint was
         * LAID OVER (the last real write of the location), not the one the
         * mint carried, so the version is not what the two are matched by:
         * the OCCURRENCE that published the row is, which is why this view
         * is scoped to one (see {@code CorpusIndex.joinOf}).</p>
         *
         * <p>The symbols are the rows' own, so this is the recording
         * answering what a read returned, not a value reconstructed
         * here.</p>
         */
        Set<String> statedReadSymbols(String locationKey);
    }

    private static final SessionJoin NO_JOIN = new SessionJoin() {
        @Override
        public JsonElement writeExpression(String locationKey, long version) {
            return null;
        }

        @Override
        public Set<String> statedReadSymbols(String locationKey) {
            return Collections.<String>emptySet();
        }
    };

    /**
     * What rows state about each location, by location.
     *
     * <p>The index every view of a session builds, so that "which symbol
     * does a row state for a read of this location" has ONE answer however
     * the session was opened -- the composer's corpus index and the flip
     * query's single session alike.  A row counts when it states the value
     * its read returned: its symbol is then bound by that row's own JOIN
     * or PIN, which is what makes it usable as the value of a read of the
     * same location the write log does not cover.</p>
     *
     * <p>{@code occurrenceId} is the scope: non-empty keeps only the rows
     * that ONE occurrence published, which is the scope a term's own reads
     * are asked in.  Empty asks the whole session, for a caller that has
     * no occurrence to ask as -- and a session whose occurrences state two
     * symbols for one location then answers nothing, rather than one of
     * them.</p>
     */
    public static Map<String, Set<String>> statedReadIndex(
            Iterable<ReadRow> reads, String occurrenceId) {
        Map<String, Set<String>> stated =
                new LinkedHashMap<String, Set<String>>();
        if (reads == null) return stated;
        String scope = occurrenceId == null ? "" : occurrenceId;
        for (ReadRow read : reads) {
            if (read == null) continue;
            if (read.symbol() == null || read.symbol().isEmpty()) continue;
            if (read.concreteValue() == null
                    || read.concreteValue().trim().isEmpty()) {
                continue;
            }
            if (!scope.isEmpty() && (read.endpoint() == null
                    || !scope.equals(read.endpoint().occurrence().id()))) {
                continue;
            }
            String key = locationKey(read.location());
            if (key.isEmpty()) continue;
            Set<String> symbols = stated.get(key);
            if (symbols == null) {
                symbols = new LinkedHashSet<String>();
                stated.put(key, symbols);
            }
            symbols.add(read.symbol());
        }
        return stated;
    }

    /**
     * The one symbol the rows state for a read of this location.
     *
     * <p>{@code ""} when no row states one.  Rows that disagree state NO
     * answer -- {@code null} -- and every caller refuses that by name:
     * picking one of two symbols would put one read's value on another
     * read, which is the reconstruction this design does not do.</p>
     */
    public static String statedReadSymbol(SessionJoin join,
                                          String locationKey) {
        Set<String> symbols = join == null || locationKey == null
                || locationKey.isEmpty()
                ? null : join.statedReadSymbols(locationKey);
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
    private final List<String> assertions = new ArrayList<String>();
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

    /** One session's write log and read rows, as the state join reads them. */
    private static SessionJoin joinOf(final SessionReader session) {
        final Map<String, String> writes = new LinkedHashMap<String, String>();
        for (edu.uva.liftlab.graphchecker.d3.contract.WriteRow write
                : session.writes()) {
            writes.put(locationKey(write.location()) + "#" + write.version(),
                    write.expressionRef());
        }
        final Map<String, Set<String>> stated =
                statedReadIndex(session.reads(), "");
        return new SessionJoin() {
            @Override
            public JsonElement writeExpression(String locationKey,
                                               long version) {
                String ref = writes.get(locationKey + "#" + version);
                return ref == null ? null
                        : session.expressions().expression(ref);
            }

            @Override
            public Set<String> statedReadSymbols(String locationKey) {
                Set<String> symbols = stated.get(locationKey);
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
        return new Lowered(value.text, "", named);
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

    /** The SMT sort one recorded Java type denotes. */
    public static String sortOf(String javaType) {
        return JavaSmtSorts.sortOfJava(javaType).smt;
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

    /** One lowered expression: its text, the symbols it names, or why not. */
    public static final class Lowered {
        private final String text;
        private final String refusal;
        private final Map<String, String> declarations;

        private Lowered(String text, String refusal,
                        Map<String, String> declarations) {
            this.text = text;
            this.refusal = refusal;
            this.declarations = Collections.unmodifiableMap(declarations);
        }

        private static Lowered refused(String reason) {
            return new Lowered("", reason,
                    new LinkedHashMap<String, String>());
        }

        public boolean ok() {
            return refusal.isEmpty() && !text.isEmpty();
        }

        public String text() {
            return text;
        }

        public String refusal() {
            return refusal;
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
        String raw = JsonText.string(expression, "_exp");
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
        String javaType = JsonText.string(expression, "_java_type");
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
        String function = JsonText.string(expression, "_place_holder_func");
        int count = JsonText.integer(expression, "_count", -1);
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
     *   <li>otherwise the symbol a READ row states for this location --
     *       the row the OCCURRENCE whose term this is published for it,
     *       which is the scope {@code join} carries.  A mint is not a
     *       write: the VM's primitive gives a declared region input a
     *       version whose value is the minted symbol, and what that read
     *       returned is stated by the reading occurrence's own row, bound
     *       by that row's own join or pin.  The row's version is the last
     *       real write the mint was laid over, not the version the mint
     *       carried, so the two are matched by the occurrence and the
     *       location and not by the version.</li>
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
        JsonObject location = JsonText.object(expression, "location");
        String key = locationKey(location);
        long version = observedVersion(expression);
        if (!key.isEmpty() && version >= 0L) {
            JsonElement written = join.writeExpression(key, version);
            if (written != null && !written.isJsonNull()) {
                JsonElement projected = observedVersionExpression(expression);
                return element(dispatch(projected != null
                                        && !projected.isJsonNull()
                                        ? projected : written, expected,
                                origin + ":join"), expression, location,
                        key, version, expected, origin);
            }
            String minted = statedReadSymbol(join, key);
            if (minted == null) {
                return unstated("ReadVersion:" + key + "@" + version + ":"
                                + join.statedReadSymbols(key),
                        "the occurrence whose term this is published two "
                                + "read rows of this location under "
                                + "different symbols, so what its read of "
                                + "it returned has no answer", expected);
            }
            if (!minted.isEmpty()) {
                return symbolTerm(symbolNode(minted,
                                JsonText.string(expression, "_java_type")),
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
        String literal = JsonText.smtLiteral(text);
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
        String javaType = JsonText.string(expression, "_java_type");
        Sort cell = JavaSmtSorts.sortOfJava(javaType);
        // The read IS of the container: the value is what it read.
        if (cell.containerState() || cell == Sort.UNKNOWN
                || expected != null && expected.containerState()) {
            return value;
        }
        long slot = JsonText.longInteger(location, "slot", -1L);
        boolean indexed = value.sort == Sort.ARRAY_VALUE && slot >= 0L
                && locationKind(JsonText.string(location, "locationKind"))
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

    /** A merge over another region's cases is a cross-session object. */
    @Override
    public Term caseMergeTerm(JsonObject expression, Sort expected,
                              String origin) {
        return cut("CaseMergeInPath:"
                        + JsonText.string(expression, "mergeId"),
                "a value merged over another region's cases reached one "
                        + "path's expression", expected);
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
            String named = JsonText.string(expression, "operation");
            if (named.isEmpty()) {
                named = field
                        ? "FIELD:" + JsonText.string(expression, "ownerClass")
                        + "@" + JsonText.longInteger(expression,
                        "fieldOffset", -1L)
                        : JsonText.string(expression, "shape");
            }
            refuse("ContainerRelation:" + (named.isEmpty() ? "unnamed"
                    : named), "");
            return free(JavaSmtSorts.sortOfJava(
                    JsonText.string(expression, "_java_type")));
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
                            + JsonText.digest(session.getKey(), 10),
                    "(distinct " + String.join(" ", held.values()) + ")");
        }
    }

    public Map<String, String> identities() {
        return opaqueIdentities;
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
                        String raw = JsonText.string(
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
        String digest = JsonText.digest(identity, 0);
        SharedTerm held = sharedTerms.get(digest);
        if (held == null) {
            held = new SharedTerm(symbols.mint("container_dag__", identity,
                    24), sort, value.text);
            sharedTerms.put(digest, held);
        }
        return new ContainerSmtCodec.Term(held.name, value.sort,
                value.integralWidth);
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
        if (declared(name)) return true;
        for (SharedTerm shared : sharedTerms.values()) {
            if (shared.name.equals(name)) return true;
        }
        return false;
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

    /** Declared symbols this lowering put in the formula. */
    public Set<String> usedSymbols() {
        return usedSymbols;
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
            while (end < line.length() && !breaks(line.charAt(end))) end++;
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
            while (to < line.length() && !breaks(line.charAt(to))) to++;
            if (to > from) names.add(line.substring(from, to));
        }
        return names;
    }

    /** Lowers one boolean constraint, with its Java definedness. */
    public String condition(JsonElement expression, String origin) {
        Term value = dispatch(expression, Sort.BOOL, origin);
        if (value == null || value.sort != Sort.BOOL) {
            refuse(origin + ":NON_BOOLEAN_CONSTRAINT", "");
            return "true";
        }
        return VmTermLowering.and(Arrays.asList(value.precondition,
                value.text));
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
        } else if (assertedOnce.add(predicate)) {
            assertions.add("(assert " + predicate + ")");
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

    public void assertNamed(String name, String formula) {
        assertions.add("(assert (! " + formula + " :named " + name + "))");
    }

    public void assertPlain(String formula) {
        if (formula == null || formula.isEmpty()
                || "true".equals(formula)) {
            return;
        }
        if (assertedOnce.add(formula)) {
            assertions.add("(assert " + formula + ")");
        }
    }

    public Set<String> unsupported() {
        return unsupported;
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
        Map<String, SharedTerm> byName = new LinkedHashMap<String, SharedTerm>();
        for (SharedTerm shared : sharedTerms.values()) {
            byName.put(shared.name, shared);
        }
        if (texts != null) {
            for (String text : texts) {
                reach(text, byName, done, ordered, 0);
            }
        }
        return ordered;
    }

    private void reach(String text, Map<String, SharedTerm> byName,
                       Set<String> done, List<Declaration> ordered,
                       int depth) {
        if (text == null || text.isEmpty() || depth > 512) return;
        for (String token : names(text)) {
            if (!done.add(token)) continue;
            SharedTerm shared = byName.get(token);
            if (shared != null) {
                // Its own dependencies first: a define-fun may name another.
                reach(shared.body, byName, done, ordered, depth + 1);
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
     * spelled; a numeral is a value and not a name.</p>
     */
    public static List<String> names(String text) {
        List<String> names = new ArrayList<String>();
        if (text == null) return names;
        int index = 0;
        while (index < text.length()) {
            char value = text.charAt(index);
            if (value == '"') {
                index = pastLiteral(text, index, '"');
                continue;
            }
            if (value == '|') {
                int end = pastLiteral(text, index, '|');
                name(names, text.substring(index + 1,
                        Math.max(index + 1, end - 1)));
                index = end;
                continue;
            }
            if (!symbolCharacter(value)) {
                index++;
                continue;
            }
            int end = index;
            while (end < text.length()
                    && symbolCharacter(text.charAt(end))) {
                end++;
            }
            name(names, text.substring(index, end));
            index = end;
        }
        return names;
    }

    /** One index past the literal that opens at {@code at}. */
    private static int pastLiteral(String text, int at, char delimiter) {
        int index = at + 1;
        while (index < text.length() && text.charAt(index) != delimiter) {
            index++;
        }
        return index < text.length() ? index + 1 : index;
    }

    /** Keeps one token if it is a name and not a numeral. */
    private static void name(List<String> names, String token) {
        if (token.isEmpty()) return;
        char first = token.charAt(0);
        if (Character.isDigit(first) || first == '-' || first == '.') return;
        names.add(token);
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

    /** Preamble and declarations, with no assertion and no check. */
    public String declarationsOnly() {
        StringBuilder query = new StringBuilder();
        appendPreamble(query);
        return legalSymbols(query.toString());
    }

    private void appendPreamble(StringBuilder query) {
        query.append("; GraphChecker Design 3 composed query").append('\n');
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
        for (Map.Entry<String, Sort> declaration
                : declarations().entrySet()) {
            query.append("(declare-const ").append(declaration.getKey())
                    .append(' ').append(declaration.getValue().smt)
                    .append(")").append('\n');
        }
        for (SharedTerm shared : sharedTerms.values()) {
            query.append("(define-fun ").append(shared.name)
                    .append(" () ").append(shared.sort.smt).append(' ')
                    .append(shared.body).append(")").append('\n');
        }
    }

    /** The query body: preamble, declarations, assertions; no check-sat. */
    public String body() {
        StringBuilder query = new StringBuilder();
        appendPreamble(query);
        for (String assertion : assertions) {
            query.append(assertion).append('\n');
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
        StringBuilder text = new StringBuilder(query.length());
        int index = 0;
        while (index < query.length()) {
            char value = query.charAt(index);
            if (value == '"' || value == '|') {
                index = copyLiteral(query, index, value, text);
                continue;
            }
            if (value == ';') {
                // A comment runs to the end of the line and is not a name.
                while (index < query.length()
                        && query.charAt(index) != '\n') {
                    text.append(query.charAt(index));
                    index++;
                }
                continue;
            }
            if (Character.isWhitespace(value) || value == '('
                    || value == ')') {
                text.append(value);
                index++;
                continue;
            }
            int end = index;
            while (end < query.length() && !breaks(query.charAt(end))) {
                end++;
            }
            String token = query.substring(index, end);
            index = end;
            text.append(simpleSymbol(token) ? token : "|" + token + "|");
        }
        return text.toString();
    }

    private static boolean breaks(char value) {
        return Character.isWhitespace(value) || value == '(' || value == ')'
                || value == '"' || value == '|';
    }

    /** Copies one string or one already-quoted symbol, closing mark and
     *  all. */
    private static int copyLiteral(String query, int start, char mark,
                                   StringBuilder text) {
        text.append(mark);
        int index = start + 1;
        while (index < query.length()) {
            char value = query.charAt(index);
            text.append(value);
            index++;
            if (value != mark) continue;
            if (mark == '"' && index < query.length()
                    && query.charAt(index) == '"') {
                text.append('"');
                index++;
                continue;
            }
            break;
        }
        return index;
    }

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

    /** Named rows of the rendered query, the formula-size measure. */
    public int namedRows() {
        return declarations().size() + sharedTerms.size()
                + assertions.size();
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
        String kind = JsonText.string(location, "locationKind");
        if (kind.isEmpty()) return "";
        String owner = JsonText.string(location, "ownerSymRid");
        if (owner.isEmpty()) {
            long rid = JsonText.longInteger(location, "ownerSymRid", 0L);
            owner = rid == 0L ? "" : Long.toString(rid);
        }
        if (owner.isEmpty()) return "";
        String slot = JsonText.string(location, "slot");
        if (slot.isEmpty()) {
            slot = Long.toString(JsonText.longInteger(location, "slot", 0L));
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
            return JsonText.longInteger(observed.getAsJsonObject(),
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
