package edu.uva.liftlab.graphchecker.d3.compose;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.d3.compose.JavaPrimitiveSmtSemantics.IntegralWidth;
import edu.uva.liftlab.graphchecker.d3.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.d3.compose.VmTermLowering.Term;
import edu.uva.liftlab.graphchecker.d3.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.d3.contract.LocationId;
import edu.uva.liftlab.graphchecker.d3.contract.LocationKind;

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
    }

    private static final SessionJoin NO_JOIN = new SessionJoin() {
        @Override
        public JsonElement writeExpression(String locationKey, long version) {
            return null;
        }
    };

    private final SmtSymbolTable symbols = new SmtSymbolTable();
    private final Map<String, Sort> declarations =
            new LinkedHashMap<String, Sort>();
    private final List<String> assertions = new ArrayList<String>();
    private final Set<String> assertedOnce = new LinkedHashSet<String>();
    /** Symbol the runtime declared -> the sort it declared it at. */
    private final Map<String, Sort> declaredSymbols;
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

    /** The lowering of one CORPUS: its rows declare every symbol. */
    public SmtLowering(Map<String, Sort> declaredSymbols) {
        this(declaredSymbols, false, null);
    }

    private SmtLowering(Map<String, Sort> declaredSymbols,
                        boolean symbolsDeclareThemselves,
                        ExpressionTable table) {
        this.declaredSymbols = declaredSymbols == null
                ? Collections.<String, Sort>emptyMap()
                : new LinkedHashMap<String, Sort>(declaredSymbols);
        this.symbolsDeclareThemselves = symbolsDeclareThemselves;
        this.table = table == null ? ExpressionTable.empty() : table;
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

    /** One session's write log, as the state join reads it. */
    private static SessionJoin joinOf(final SessionReader session) {
        final Map<String, String> writes = new LinkedHashMap<String, String>();
        for (edu.uva.liftlab.graphchecker.d3.contract.WriteRow write
                : session.writes()) {
            writes.put(locationKey(write.location()) + "#" + write.version(),
                    write.expressionRef());
        }
        return new SessionJoin() {
            @Override
            public JsonElement writeExpression(String locationKey,
                                               long version) {
                String ref = writes.get(locationKey + "#" + version);
                return ref == null ? null
                        : session.expressions().expression(ref);
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
        for (Map.Entry<String, Sort> declaration : declarations.entrySet()) {
            if (mentions(value.text, declaration.getKey())) {
                named.put(declaration.getKey(), declaration.getValue().smt);
            }
        }
        return new Lowered(value.text, "", named);
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

    private static boolean symbolCharacter(char value) {
        return Character.isLetterOrDigit(value) || value == '_'
                || value == '.' || value == '$';
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
        this.openSideConditions = new ArrayList<String>();
        this.openRefusals = new ArrayList<String>();
        this.scope = sessionId == null ? "" : sessionId;
        this.join = sessionJoin == null ? NO_JOIN : sessionJoin;
    }

    /** Closes it, answering the side conditions its lowering raised. */
    public List<String> end() {
        List<String> conditions = openSideConditions == null
                ? Collections.<String>emptyList() : openSideConditions;
        openSideConditions = null;
        openRefusals = null;
        scope = "";
        join = NO_JOIN;
        return conditions;
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
        if ("SYMBOLIC_NULL".equals(raw)) return Term.of("nullRef", Sort.REF);
        if ("V".equals(raw)) return Term.of("true", Sort.BOOL);
        String javaType = JsonText.string(expression, "_java_type");
        Sort encoded = JavaSmtSorts.sortOfJava(javaType);
        Sort sort = expected == Sort.MAP || expected == Sort.ARRAY_VALUE
                ? expected
                : encoded != Sort.VALUE ? encoded
                : expected == null ? Sort.REF : expected;
        Sort declared = declaredSymbols.get(raw);
        if (declared != null) {
            // The declaration is the mint, and wins over the shape of the
            // node the symbol turned up in: one variable has one sort.
            declare(raw, declared);
            usedSymbols.add(raw);
            return Term.of(raw, declared,
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
                "no root mint, attach or decision of this corpus declares "
                        + "this symbol", sort);
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
                return dispatch(written, expected, origin + ":join");
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
            refuse("ContainerRelation:"
                    + JsonText.string(expression, "operation"), "");
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
                return value == null ? null : new ContainerSmtCodec.Term(
                        value.text,
                        VmTermLowering.containerSortOf(value.sort));
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
                    unsupported("CannotBox:" + javaType);
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
        String identity = sort.name() + SEPARATOR + value.text;
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

    /** Declares one name once; a second, different sort is a defect. */
    public void declare(String name, Sort sort) {
        Sort held = declarations.get(name);
        if (held == null) {
            declarations.put(name, sort);
            return;
        }
        if (held != sort) {
            throw new IllegalStateException("SMT name " + name
                    + " declared as " + held + " and " + sort);
        }
    }

    /** Whether one name is declared in this query. */
    public boolean declared(String name) {
        return declarations.containsKey(name);
    }

    public Map<String, Sort> declarations() {
        return Collections.unmodifiableMap(declarations);
    }

    /** Declared symbols this lowering put in the formula. */
    public Set<String> usedSymbols() {
        return usedSymbols;
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

    /** Preamble and declarations, with no assertion and no check. */
    public String declarationsOnly() {
        StringBuilder query = new StringBuilder();
        appendPreamble(query);
        return query.toString();
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
        for (Map.Entry<String, Sort> declaration : declarations.entrySet()) {
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
        return query.toString();
    }

    /** The whole query, at the assertions it holds. */
    public String render() {
        return body() + "(check-sat)\n";
    }

    /** Named rows of the rendered query, the formula-size measure. */
    public int namedRows() {
        return declarations.size() + sharedTerms.size() + assertions.size();
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
