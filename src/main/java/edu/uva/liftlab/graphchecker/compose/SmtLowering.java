package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Reason;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Term;
import edu.uva.liftlab.graphchecker.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.FloatingKind;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.IntegralWidth;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.smt.VmRows;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
import static edu.uva.liftlab.graphchecker.smt.VmExpressionIr.isPrimitiveIntExpression;
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
         * {@link #reachedSymbols} names the recorded state a
         * {@code container_dag__} stands for.
         *
         * <p>Placeholder rows are excluded: their {@code observedVersion} is
         * the write they were laid over, so listing them here would put the
         * minted value on that write's readers.</p>
         */
        Set<String> readSymbols(String locationKey, long version);
    }

    /** The join of no session: it states nothing. */
    public static final SessionJoin NO_JOIN = new SessionJoin() {
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
    /** What this corpus states at two sorts: name -> "<held> and <new>". */
    private final Map<String, String> sortConflicts =
            new LinkedHashMap<String, String>();
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
    private final Set<String> unsupported = new LinkedHashSet<String>();
    private final Map<String, String> unsupportedDetail =
            new LinkedHashMap<String, String>();
    private final Set<String> cuts = new LinkedHashSet<String>();
    private final Set<String> integralDomains = new LinkedHashSet<String>();
    private boolean usesJavaIntString;

    /**
     * Where a symbol's declaration comes from.  A CORPUS lowering knows every
     * declared symbol, so an undeclared scalar leaf is the propagation cut.
     * A SESSION lowering sees one expression, so the leaf's own
     * {@code _java_type} declares it.  The lowering itself is the same.
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
    private final Deque<Frame> frames = new ArrayDeque<Frame>();

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
     */
    public static SmtLowering forSession(SessionReader session,
                                         SessionJoin join) {
        SmtLowering lowering = new SmtLowering(
                Collections.<String, Sort>emptyMap(), true,
                session.expressions());
        lowering.scope = session.sessionId();
        lowering.join = join;
        return lowering;
    }

    /**
     * One session's write log and read rows, as the state join reads them;
     * the only implementation, built once per session ({@code Corpus#join}).
     */
    public static SessionJoin joinOf(final SessionReader session) {
        final Map<String, String> writes = new LinkedHashMap<String, String>();
        for (WriteRow write : session.writes()) {
            writes.put(locationKey(write.location()) + "#" + write.version(),
                    write.expressionRef());
        }
        // A row counts when it states a symbol (its JOIN or PIN binds it):
        // by mint version, else by the location and version it observed.
        final Map<Long, Set<String>> minted =
                new LinkedHashMap<Long, Set<String>>();
        final Map<String, Set<String>> observed =
                new LinkedHashMap<String, Set<String>>();
        for (ReadRow read : session.reads()) {
            if (read == null || read.symbol() == null
                    || read.symbol().isEmpty()) {
                continue;
            }
            if (read.mintVersion() >= 0L) {
                add(minted, read.mintVersion(), read.symbol());
            } else if (read.observedVersion() >= 0L) {
                add(observed, locationKey(read.location()) + "#"
                        + read.observedVersion(), read.symbol());
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
     * One expression of this session, lowered to text and sort, or a named
     * refusal; {@link #reference} is the rule, so its definedness is a fact
     * of this lowering ({@link #facts}).  Callers ask
     * {@link #declarations()} for the names it reaches.
     */
    public Lowered lower(String expressionRef) {
        List<String> refusalsBefore =
                new ArrayList<String>(unsupported);
        Term value = reference(expressionRef, "lower:" + expressionRef);
        if (value == null) {
            return Lowered.refused("ABSENT_EXPRESSION:" + expressionRef);
        }
        List<String> refused = new ArrayList<String>(unsupported);
        refused.removeAll(refusalsBefore);
        if (!refused.isEmpty()) return Lowered.refused(refused.get(0));
        return new Lowered(value.text, value.sort.smt, "");
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
        Term value = dispatch(expression, null, origin);
        sideCondition(value.precondition);
        return value;
    }

    /** One lowered expression: its text, its sort, its symbols, or why not. */
    public static final class Lowered {
        private final String text;
        private final String sort;
        private final String refusal;

        private Lowered(String text, String sort, String refusal) {
            this.text = text;
            this.sort = sort;
            this.refusal = refusal;
        }

        private static Lowered refused(String reason) {
            return new Lowered("", "", reason);
        }

        public boolean ok() {
            return refusal.isEmpty() && !text.isEmpty();
        }

        public String text() {
            return text;
        }

        /**
         * The SMT sort a variable bound to this text must be declared at;
         * not the row's Java type, which can differ for container state.
         */
        public String sort() {
            return sort;
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
     * Opens one conjunction in one session's scope, with the session's
     * expression table, against which {@link #statedTerm} resolves
     * references.  Identities and side conditions are per execution: one
     * constant for two sessions' objects makes satisfiable paths unsat.
     */
    public void begin(String sessionId, SessionJoin sessionJoin,
                      ExpressionTable expressions) {
        // NESTED, not replaced: an arm is lowered in its producer's scope
        // mid-path; overwriting the path's frame would leave the rest of the
        // path with no join, no table and no refusal sink.
        frames.push(new Frame(openSideConditions, openRefusals, scope, join,
                openTable));
        this.openSideConditions = new ArrayList<String>();
        this.openRefusals = new ArrayList<String>();
        this.scope = sessionId;
        this.join = sessionJoin;
        this.openTable = expressions;
    }

    /** Closes it, answering the side conditions its lowering raised. */
    public List<String> end() {
        List<String> conditions = openSideConditions;
        Frame previous = frames.pop();
        openSideConditions = previous.conditions;
        openRefusals = previous.refusals;
        scope = previous.scope;
        join = previous.join;
        openTable = previous.table;
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
    // Results and their definedness.
    // ------------------------------------------------------------------

    /** A named refusal, as a fresh value of the refused construct's sort. */
    private Term refuse(Reason reason, String origin, String detail,
                        Sort sort) {
        refuse(reason.composedSubject(origin, detail), "");
        return free(sort);
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
     * non-null String, and every operand evaluated.
     */
    private static String stringDefinedness(List<Term> dereferenced,
                                            List<Term> evaluated) {
        List<String> values = new ArrayList<String>();
        for (Term value : dereferenced) {
            if (value.sort != Sort.STRING) {
                values.add("false");
                continue;
            }
            values.add(value.precondition);
            String nullness = value.stringNullness.isEmpty()
                    ? "true" : value.stringNullness;
            values.add("false".equals(value.stringNullness) ? "true"
                    : "(not " + nullness + ")");
        }
        for (Term value : evaluated) {
            values.add(value.precondition);
        }
        return and(values);
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
        if ("V".equals(raw)) return Term.of("true", Sort.BOOL);
        String javaType = primitiveString(expression, "_java_type");
        Sort encoded = JavaSmtSorts.sortOfJava(javaType);
        Sort sort = expected == Sort.MAP || expected == Sort.ARRAY_VALUE
                ? expected
                : encoded != Sort.VALUE ? encoded
                : expected == null ? Sort.REF : expected;
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
                            + "reference holding it was null", expected);
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
            return free(Sort.INT);
        }
        String name = symbols.mint("environment__",
                scope + SEPARATOR + function + "#" + count, 10);
        declare(name, Sort.INT);
        assertJavaIntegralDomain(name, "J");
        return Term.of(name, Sort.INT, IntegralWidth.JAVA_LONG);
    }

    /**
     * A read, joined to the write version it observed: JOIN, then PIN, then
     * REFUSE (the same rule as {@code ContainerSmtCodec.field}).  Never
     * enumerate retained versions for the solver to pick from.
     *
     * <p>JOIN asks the rows, in this session: the {@code WriteRow} of this
     * location and version (the writer's propagation); otherwise the
     * placeholder row whose {@code mintVersion} is this version (a mint is
     * not a write).</p>
     *
     * <p>The node's own {@code observedVersion} expression is the projection
     * this read performed (e.g. {@code SIZE(state)}); it is used only once a
     * write row has stated the version.  Consulted without one, it binds the
     * read to a value no row stands behind.</p>
     */
    private Term guardedReadTerm(JsonObject expression, Sort expected,
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
                        key, version, expected), key, version);
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
                        primitiveString(expression, "_java_type")), expected);
            }
        }
        JsonElement concrete = expression.get("concreteValue");
        if (concrete != null && !concrete.isJsonNull()) {
            return dispatch(concrete, expected, origin + ":pinned");
        }
        return unstated("Read:" + key + "@" + version,
                "no write of this location at this version in this session, "
                        + "and the recording states no value it returned",
                expected);
    }

    /**
     * Records the read rows' symbols on the named container subterm the
     * read produced, where {@link #reachedSymbols} finds them (the inlined
     * body never names the cell).  A subterm two reads produce carries both.
     */
    private Term observing(Term value, String key, long version) {
        SharedTerm shared = sharedByName.get(value.text);
        if (shared != null) {
            shared.states.addAll(join.readSymbols(key, version));
        }
        return value;
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
     * pins and {@code concreteValue} alike: a reference or {@code "N"} goes
     * through {@link #symbolTerm}; a scalar is its literal.
     */
    Term statedValue(String concreteValue, String javaType) {
        String text = concreteValue == null ? "" : concreteValue.trim();
        if (text.isEmpty()) return null;
        if (VmExpressionIr.SYMBOLIC_NULL.equals(text)
                || VmRows.referencedObjectRid(text) > 0L) {
            return symbolTerm(symbolNode(text, javaType), null);
        }
        String literal = smtLiteral(text);
        if (literal.isEmpty()) return null;
        Sort sort = JavaSmtSorts.sortOfJava(javaType);
        if (!sort.scalar()) return null;
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
                        + "which cell of it the read returned", cell);
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

    // ------------------------------------------------------------------
    // Identities.
    // ------------------------------------------------------------------

    /**
     * One execution-local identity, opaque but not free: it is non-null and
     * distinct from other rids of its session, both recorded facts.  Left
     * unsaid, a model can null a reference or merge two keys.
     */
    private String opaque(String raw, Sort sort) {
        String name = symbols.mint("identity__",
                scope + SEPARATOR + sort + SEPARATOR + raw, 10);
        declare(name, sort);
        boolean minted = opaqueIdentities.put(name, raw) == null;
        long rid = VmRows.referencedObjectRid(raw);
        if (minted && sort == Sort.REF && rid > 0L) {
            assertPlain("(not (= " + name + " nullRef))");
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

    private ContainerSmtCodec.Host host(final String origin) {
        return new ContainerSmtCodec.Host() {
            @Override
            public ContainerSmtCodec.Term state(
                    JsonElement identity, ContainerSmtCodec.Sort shape) {
                Sort stateSort = shape == ContainerSmtCodec.Sort.INDEXED
                        ? Sort.ARRAY_VALUE : Sort.MAP;
                Term reference = dispatch(identity, Sort.REF,
                        origin + ":container-state");
                if (reference.sort != Sort.REF) {
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
                // Keep the Java width: shift and bitwise operators are typed
                // (ISHR is not LSHR) and are ambiguous without it.
                return new ContainerSmtCodec.Term(value.text,
                        VmTermLowering.containerSortOf(value.sort),
                        value.integralWidth);
            }

            @Override
            public ContainerSmtCodec.Term box(JsonElement expression) {
                Term value = dispatch(expression, null,
                        origin + ":container-value");
                String javaType =
                        VmTermLowering.expressionJavaType(expression);
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
        String integral = ContainerStateModel.boxIntegral(value.text, javaType);
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
         * The recorded state this subterm is the value of (the read rows'
         * symbols).  Not derivable from the body, whose base is often an
         * empty container rather than a symbol.
         */
        private final Set<String> states = new LinkedHashSet<String>();

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
        return new ContainerSmtCodec.Term(held.name, value.sort,
                value.integralWidth, value.indexedSize);
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
     * Puts a name the recording already states into the query, answering
     * whether it is stated; for callers holding text rather than leaves.
     */
    public boolean declareStated(String name) {
        Declared held = declarations.get(name);
        if (held == null || !held.stated) return false;
        put(name, held.sort, true);
        return true;
    }

    /**
     * One name, one sort.  A second sort is refused by name (dropping the
     * path) and kept in {@link #sortConflicts} for a BLOCKING gap, never
     * thrown.  The FIRST declaration stands: re-sorting would make earlier
     * assertions ill-sorted and z3 would answer {@code (error ...)}.
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
     * Whether this query gives one name a meaning at all: a
     * {@code declare-const} or a container subterm's {@code define-fun}.
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
        return free(sort);
    }

    private Term unstated(String subject, String detail, Sort sort) {
        refuse(UNSTATED + ":" + subject, detail);
        return free(sort);
    }

    /**
     * One fresh unconstrained value for a refused construct: FRESH PER
     * CONSTRUCT, NEVER PER REASON.  A refusal knows nothing about the value,
     * not even equality with another refused one; sharing one variable
     * makes paths spuriously UNSAT (e.g. {@code (>= u 0)} and its negation
     * over one {@code u}).
     */
    private Term free(Sort sort) {
        Sort declared = sort == null || sort == Sort.UNKNOWN
                ? Sort.VALUE : sort;
        String name = symbols.mint("unsupported__",
                scope + "#" + declared + "#" + freeConstants++, 10);
        declare(name, declared);
        return Term.of(name, declared, declared == Sort.INT
                ? IntegralWidth.JAVA_INT : IntegralWidth.NONE);
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
     * facts frees a boundary CLOSURE-V2 SS3 forbids freeing.
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
        for (String cut : cuts) {
            named.put(cut,
                    unsupportedDetail.getOrDefault(CUT + ":" + cut, ""));
        }
        return named;
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
                reach(text, done, ordered, 0);
            }
        }
        return ordered;
    }

    private void reach(String text, Set<String> done,
                       List<Declaration> ordered, int depth) {
        if (text == null || text.isEmpty() || depth > 512) return;
        for (String token : SmtNames.names(text)) {
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
     * The recording's symbols of one term, THROUGH the container subterms it
     * names (same reachability as {@link #reachedBy}); minted names are
     * walked through, never reported.  A guard over a map read is just
     * {@code container_dag__...}, so the text alone names nothing.
     *
     * <p>Two outputs: {@code into} is what the term SAYS (recorded names);
     * {@code states} is what it RESTS ON, the read rows behind named
     * container subterms ({@link SharedTerm#states}, the v_C rule of
     * CLOSURE-V2).  The closure planner may pass one set for both; the flip
     * query must not, or it declares a container variable the query never
     * names.</p>
     */
    public Set<String> reachedSymbols(String text, Set<String> into,
                                      Set<String> states) {
        reachedSymbols(text, new LinkedHashSet<String>(), into, states, 0);
        return into;
    }

    /** What these texts SAY, together; what they rest on is not asked. */
    Set<String> reachedSymbols(Iterable<String> texts) {
        Set<String> into = new LinkedHashSet<String>();
        for (String text : texts) reachedSymbols(text, into, null);
        return into;
    }

    private void reachedSymbols(String text, Set<String> seen,
                                Set<String> into, Set<String> states,
                                int depth) {
        if (text == null || text.isEmpty() || depth > 512) return;
        for (String name : SmtNames.names(text)) {
            if (SmtNames.BUILTIN.contains(name) || !seen.add(name)) continue;
            SharedTerm shared = sharedByName.get(name);
            if (shared != null) {
                // v_C (CLOSURE-V2): a term reaching the dag rests on the
                // state it stands for, which its body does not name.
                if (states != null) states.addAll(shared.states);
                reachedSymbols(shared.body, seen, into, states, depth + 1);
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
        if (usesJavaIntString) {
            lines.add(VmTermLowering.JAVA_INT_TO_STRING);
        }
        lines.add(JavaPrimitiveSmtSemantics.INT_WRAP_DEFINITION);
        lines.add(JavaPrimitiveSmtSemantics.LONG_WRAP_DEFINITION);
        return lines;
    }

    private void appendPreamble(StringBuilder query,
                                Iterable<String> texts) {
        query.append("; GraphChecker composed query").append('\n');
        // Must precede the logic: without it (get-unsat-core) errors.
        query.append("(set-option :produce-unsat-cores true)").append('\n');
        // Only the part of the one preamble the query reaches.
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

    // ------------------------------------------------------------------
    // Dispatch.
    // ------------------------------------------------------------------

    /**
     * Lowers one recorded VM expression of any kind.  Never null: a refused
     * construct is a fresh value of its sort, named in the open refusals.
     */
    public Term dispatch(JsonElement expression, Sort expected,
                        String origin) {
        Term value = lowered(expression, expected, origin);
        if (expression != null && expression.isJsonObject()) {
            JsonElement observed = expression.getAsJsonObject()
                    .get(VmRows.RECORDED_READING);
            if (observed != null && !observed.isJsonNull()) {
                recordedReading(value, observed, origin);
            }
        }
        return value;
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
     * A Java library call: this lowering proves no call's exact value
     * relation, so each is a named gap at the sort the call returns.
     */
    private Term methodTerm(JsonObject expression, String origin) {
        String method = optionalString(expression, "_name");
        if (VmExpressionIr.isJavaParseInt(method)) {
            // Nothing proves the argument is exactly a decimal int rendering.
            return refuse(Reason.MODEL_SEMANTICS_MISSING, origin,
                    "java/lang/Integer.parseInt:PARSE_INT_NOT_LOWERED",
                    Sort.INT);
        }
        if (VmExpressionIr.isJavaSplitElement(method)) {
            return refuse(Reason.MODEL_SEMANTICS_MISSING, origin,
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

    /** One recorded {@code BinaryExpression}. */
    private Term binary(JsonObject expression, String origin) {
        String operator = JavaPrimitiveSmtSemantics.canonicalVmOperator(
                optionalString(expression, "_op"));
        JsonElement leftExpression = expression.get("_left");
        if (leftExpression == null || leftExpression.isJsonNull()) {
            return unary(expression, operator, origin);
        }
        Term left = dispatch(leftExpression, null, origin + ":left");
        Term right = dispatch(expression.get("_right"), left.sort,
                origin + ":right");
        // A JVM reference comparison against the integer 0 is a null test.
        if (left.sort != right.sort && right.isZero()
                && left.sort == Sort.REF) {
            right = result("nullRef", Sort.REF);
        } else if (left.sort != right.sort && left.isZero()
                && right.sort == Sort.REF) {
            left = result("nullRef", Sort.REF);
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
     * Java {@code ==} between two Strings is reference identity.  Three
     * cases close it exactly and the rest stays refused.
     */
    private Term stringIdentity(JsonObject expression, String operator,
                                Term left, Term right, String origin) {
        if (ContainerSmtCodec.handlesFieldBinding(expression)) {
            Term symbol = ContainerSmtCodec.handlesField(
                    expression.get("_left")) ? right : left;
            String materialization = ContainerSmtCodec
                    .materializedStringEquality(left.text, right.text,
                            symbol.stringNullness);
            if (materialization.isEmpty()) {
                return refuse(Reason.JAVA_STRING_NULLNESS_UNKNOWN, origin,
                        "MATERIALIZATION:" + operator, Sort.BOOL);
            }
            return result(materialization, Sort.BOOL, left, right);
        }
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
        String operation = optionalString(expression, "_name");
        boolean negated = optionalBool(expression, "_is_not", false);
        JsonArray params = array(expression, "_param_list");
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
        if ("toString".equals(operation)) {
            if (params.size() != 1
                    || !isPrimitiveIntExpression(params.get(0))) {
                return codecGap(operation, "REQUIRES_ONE_PRIMITIVE_INT",
                        origin, Sort.STRING);
            }
            Term integer = dispatch(params.get(0), Sort.INT,
                    origin + ":toString");
            if (integer.sort != Sort.INT) {
                return codecGap(operation, "NON_INT_TERM", origin,
                        Sort.STRING);
            }
            assertJavaIntegralDomain(integer.text, "I");
            // Java's decimal Integer.toString, defined where the int is.
            usesJavaIntString = true;
            return Term.nonNullString("(java_int_to_string " + integer.text
                    + ")", integer.precondition);
        }
        return codecGap(firstNonBlank(operation, "unknown"),
                "UNSUPPORTED_OPERATION", origin, Sort.STRING);
    }

    /** Java String.equals requires a non-null receiver but accepts null. */
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
                    "(= " + receiver.text + " " + argument.text + ")"));
        }
        return booleanStringResult(predicate, negated, stringDefinedness(
                Collections.singletonList(receiver),
                Collections.singletonList(argument)));
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
