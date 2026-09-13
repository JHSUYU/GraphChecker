package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.IntegralWidth;
import edu.uva.liftlab.graphchecker.concolic.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.concolic.VmTermLowering.Term;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.concolic.VmTermLowering.and;

/**
 * The SMT lowering of one already-resolved replay expression.
 *
 * <p>Every value reaching this class has been through
 * {@link InSessionReadResolver}, so a shared-state read is already the
 * expression of the write that replay read.  There is therefore no arm, no
 * candidate, no selector over writers and no last-writer-wins axiom here:
 * the only things a leaf can be are a root the recording left free, a
 * literal, or a container relation over those.  A read node that survives
 * resolution is not something to reconstruct -- it is the propagation cut,
 * and it is refused under that name.</p>
 *
 * <p>What the lowering itself knows about Java stays in
 * {@link VmLoweringCore}, {@link VmTermLowering} and
 * {@link ContainerSmtCodec}; this class only states the three policies
 * those leave to their caller and mints names.</p>
 */
final class PathMergeLowering extends VmLoweringCore {
    /** The one refusal that means "propagation did not carry the value". */
    static final String CUT = "PROPAGATION_CUT";

    private final SmtSymbolTable symbols = new SmtSymbolTable();
    private final Map<String, Sort> declarations = new LinkedHashMap<>();
    private final Map<String, String> functions = new LinkedHashMap<>();
    private final List<String> assertions = new ArrayList<>();
    private final Set<String> assertedOnce = new LinkedHashSet<>();
    /** Raw VM symbol -> the root inventory row that declares it. */
    private final Map<String, JsonObject> declaredRoots;
    /** Solver term -> the raw VM symbol it stands for. */
    private final Map<String, String> rootTerms = new LinkedHashMap<>();
    /** Solver term -> the execution-local identity it stands for. */
    private final Map<String, String> opaqueIdentities =
            new LinkedHashMap<>();
    /**
     * Side conditions the lowering of the path now being merged produced.
     *
     * <p>A container access states a definedness fact about the state it
     * reads -- that a cell holds the tag it is unboxed at, say.  That fact
     * is true where the path ran, and nowhere else: asserted globally it
     * would constrain the alternatives, so it is conjoined into the path
     * whose lowering raised it.</p>
     */
    private List<String> pathSideConditions;
    /**
     * Which replay's values are being lowered.
     *
     * <p>An execution-local identity -- the object a parameter referred to,
     * the container a state symbol names -- is local to the execution that
     * produced it.  Two replays' expressions mention the same VM symbol for
     * two different objects, so a name minted without the replay in it makes
     * one constant carry both, and the two paths' facts about it contradict:
     * a disjunction of perfectly satisfiable paths comes back unsat.</p>
     */
    private String pathScope = "";
    /** Allocated container reference -> the state sort it carries. */
    private final Map<String, Sort> containerStates = new LinkedHashMap<>();
    private final Set<String> unsupported = new LinkedHashSet<>();
    private final Map<String, String> unsupportedDetail =
            new LinkedHashMap<>();
    /** Subjects refused because a value was owed and a placeholder came. */
    private final Set<String> cuts = new LinkedHashSet<>();
    /**
     * Associative reads that answered out of the absent-key default.
     *
     * <p>A key a writer removed is absent <em>because</em> of the removal,
     * and a witness resting on it says something about the program.  A key
     * nothing ever put is absent in the recording too: its null is the
     * default of an untouched map, and a witness resting on that has
     * explained nothing.  Each such read is named here with the condition
     * under which it missed, so the claim can tell the two apart.</p>
     */
    private final Map<String, JsonObject> absentKeyDefaults =
            new LinkedHashMap<>();
    private final Set<String> integralDomains = new LinkedHashSet<>();
    private boolean usesJavaIntString;

    PathMergeLowering(Map<String, JsonObject> declaredRoots) {
        this.declaredRoots = declaredRoots == null
                ? Collections.<String, JsonObject>emptyMap() : declaredRoots;
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

    /** Records one refusal; a cut is the subset the gate reads. */
    private void refuse(String subject, String detail) {
        unsupported.add(subject);
        if (detail != null && !detail.isEmpty()) {
            unsupportedDetail.put(subject, detail);
        }
    }

    private Term cut(String subject, String detail, Sort sort) {
        cuts.add(subject);
        refuse(CUT + ":" + subject, detail);
        return free(sort == null ? Sort.VALUE : sort);
    }

    @Override
    public Term dependent(Term result, Term... inputs) {
        List<String> values = new ArrayList<>();
        values.add(result.precondition);
        if (inputs != null) {
            for (Term input : inputs) {
                if (input != null) values.add(input.precondition);
            }
        }
        return result.withPrecondition(and(values));
    }

    @Override
    public Sort castSort(String descriptor) {
        return JavaSmtSorts.castSort(descriptor);
    }

    @Override
    Sort sortOfJavaType(String javaType) {
        return JavaSmtSorts.sortOfJava(javaType);
    }

    /**
     * Definedness rides on the term, as it does in final composition: an
     * operand Java evaluated only conditionally must constrain nothing
     * where Java never ran it.
     */
    @Override
    Term definedResult(String text, Sort sort, IntegralWidth width,
                       String definedness, Term... inputs) {
        return dependent(Term.of(text, sort, width, "", "", definedness),
                inputs);
    }

    @Override
    Term shortCircuit(String text, Term left, Term right,
                      boolean conjunction) {
        String rightEvaluated = conjunction ? left.text
                : "(not " + left.text + ")";
        return Term.of(text, Sort.BOOL).withPrecondition(
                and(Arrays.asList(left.precondition,
                        "(=> " + rightEvaluated + " " + right.precondition
                                + ")")));
    }

    @Override
    String stringDefinedness(String origin, String operation,
                             List<Term> dereferenced, List<Term> evaluated) {
        List<String> values = new ArrayList<>();
        for (Term value : dereferenced) {
            if (value == null || value.sort != Sort.STRING) {
                values.add("false");
                continue;
            }
            values.add(value.precondition);
            values.add("false".equals(value.stringNullness) ? "true"
                    : "(not " + firstNonBlank(value.stringNullness, "true")
                    + ")");
        }
        for (Term value : evaluated) {
            values.add(value == null ? "false" : value.precondition);
        }
        return and(values);
    }

    @Override
    void assertJavaIntegralDomain(String term, Sort sort, String javaType,
                                  String identity) {
        if (sort != Sort.INT || term == null || term.isEmpty()) return;
        JavaPrimitiveSmtSemantics.IntegralDomain domain =
                JavaPrimitiveSmtSemantics.domainOfJavaType(javaType);
        if (domain == null || !integralDomains.add(term)) return;
        assertions.add("(assert " + VmTermLowering.integralRange(
                domain.lower, term, domain.upper) + ")");
    }

    @Override
    void noteJavaIntToString() {
        usesJavaIntString = true;
    }

    @Override
    public VmTermLowering.RenderedInteger renderedInteger(
            JsonElement element, String origin) {
        // Proving String.split round trips needs the split evidence the old
        // composition kept per read.  Naming it is the honest answer.
        return new VmTermLowering.RenderedInteger(null,
                "ROUNDTRIP_NOT_PROVED_NO_SPLIT_EVIDENCE");
    }

    @Override
    public void assertJavaIntRange(Term integer) {
        if (integer == null || integer.sort != Sort.INT) return;
        assertJavaIntegralDomain(integer.text, Sort.INT, "I", integer.text);
    }

    // ------------------------------------------------------------------
    // Leaves.
    // ------------------------------------------------------------------

    @Override
    Term symbolTerm(JsonObject expression, Sort expected, String origin) {
        String raw = optionalString(expression, "_exp");
        if (VmExpressionIr.SYMBOLIC_NULL.equals(raw)) {
            return Term.of("nullRef", Sort.REF);
        }
        if ("V".equals(raw)) return Term.of("true", Sort.BOOL);
        String javaType = optionalString(expression, "_java_type");
        Sort encoded = JavaSmtSorts.sortOfJava(javaType);
        Sort sort = expected == Sort.MAP || expected == Sort.ARRAY_VALUE
                ? expected
                : encoded != Sort.VALUE ? encoded
                : expected == null ? Sort.REF : expected;
        JsonObject root = declaredRoots.get(raw);
        if (root == null) {
            // A reference or container identity is not a value propagation
            // owes: it is which object this execution ran on, and nothing
            // about the failure follows from its spelling.  It becomes one
            // opaque constant, recorded so the ledger says it was free.
            if (sort == Sort.REF || sort.containerState()) {
                return Term.of(opaque(raw, sort), sort);
            }
            // A scalar with no root behind it is a value the recording
            // never explained: the cut, under its own name.
            return cut("UndeclaredFreeSymbol:" + raw,
                    "no configured or manual symbolization event declares "
                            + "this symbol", sort);
        }
        String name = rootTerm(root, raw, sort);
        assertJavaIntegralDomain(name, sort,
                firstNonBlank(optionalString(root, "javaType"), javaType),
                raw);
        return Term.of(name, sort, IntegralWidth.NONE, "", "", "true");
    }

    /** One execution-local identity, named once and left free. */
    private String opaque(String raw, Sort sort) {
        String name = symbols.mint("identity__",
                pathScope + "\0" + sort + "\0" + raw, 10);
        declare(name, sort);
        opaqueIdentities.put(name, raw);
        return name;
    }

    /** The one solver name of one declared root. */
    String rootTerm(JsonObject root, String raw, Sort sort) {
        String name = JavaSmtSorts.smtName(firstNonBlank(
                optionalString(root, "symbol"), "sym__" + raw));
        declare(name, sort);
        rootTerms.put(name, raw);
        return name;
    }

    @Override
    Term placeholderTerm(JsonObject expression, String origin) {
        String function = optionalString(expression, "_place_holder_func");
        int count = JsonFields.optionalInteger(expression, "_count", -1);
        if (!"currentTimeMills".equals(function) || count < 1) {
            refuse("PlaceholderExpression:"
                    + firstNonBlank(function, "unknown") + "#" + count, "");
            return free(Sort.INT);
        }
        String identity = function + "#" + count;
        String name = symbols.mint("environment__", identity, 10);
        declare(name, Sort.INT);
        assertJavaIntegralDomain(name, Sort.INT, "J", identity);
        return Term.of(name, Sort.INT, IntegralWidth.JAVA_LONG);
    }

    /**
     * A read the resolver could not turn into a value.
     *
     * <p>This is the propagation cut itself.  The old composition answered
     * it by enumerating the versions the VM retained and letting the solver
     * pick one; that choice is exactly what made the formula a
     * reconstruction rather than a merge, so here it is refused.</p>
     */
    @Override
    Term guardedReadTerm(JsonObject expression, Sort expected,
                         String origin) {
        return cut("UnresolvedSharedRead:"
                        + InSessionReadResolver.sessionLocation(
                        JsonFields.object(expression, "location")),
                "the replay's own value for this read was not resolved",
                expected);
    }

    /** A merge over a producer's cases is a cross-path object; not here. */
    @Override
    Term caseMergeTerm(JsonObject expression, Sort expected, String origin) {
        return cut("CaseMergeInPath:"
                        + optionalString(expression, "mergeId"),
                "a value merged over another region's cases reached one "
                        + "path's expression", expected);
    }

    @Override
    Term containerTerm(JsonObject expression, boolean field, String origin) {
        ContainerSmtCodec.Term value = field
                ? ContainerSmtCodec.field(expression, host(origin))
                : ContainerSmtCodec.term(expression, host(origin));
        if (value == null) {
            refuse("ContainerRelation:"
                    + optionalString(expression, "operation"), "");
            return free(expected(expression));
        }
        Sort sort = VmTermLowering.sortOfContainer(value.sort);
        if (sort == Sort.UNKNOWN) {
            refuse(origin + ":CONTAINER_STATE_USED_AS_VALUE", "");
            return free(Sort.VALUE);
        }
        // The codec knows the Java width of a size or an index; dropping it
        // would make the next arithmetic operand ambiguous.
        return Term.vm(value.text, sort, value.integralWidth);
    }

    private static Sort expected(JsonObject expression) {
        return JavaSmtSorts.sortOfJava(
                optionalString(expression, "_java_type"));
    }

    @Override
    Term splitElementTerm(JsonObject expression, String origin) {
        refuse("MODEL_SEMANTICS_MISSING:java/lang/String.splitElement", "");
        return free(Sort.STRING);
    }

    @Override
    Sort methodResultSort(JsonObject expression, String origin) {
        Term result = dispatch(expression.get("_res_exp"), null, origin);
        return result == null ? Sort.VALUE : result.sort;
    }

    // ------------------------------------------------------------------
    // Containers.
    // ------------------------------------------------------------------

    private ContainerSmtCodec.Host host(final String origin) {
        return new ContainerSmtCodec.Host() {
            @Override
            public ContainerSmtCodec.Term state(JsonElement identity,
                                                ContainerSmtCodec.Sort shape) {
                Sort stateSort = shape == ContainerSmtCodec.Sort.INDEXED
                        ? Sort.ARRAY_VALUE : Sort.MAP;
                Term reference = dispatch(identity, Sort.REF,
                        origin + ":container-state");
                if (reference == null || reference.sort != Sort.REF) {
                    if (identity != null && identity.isJsonObject()) {
                        String raw = optionalString(
                                identity.getAsJsonObject(), "_exp");
                        if (!raw.isEmpty()) {
                            String name = symbols.mint("container__",
                                    pathScope + "\0" + shape
                                            + "\0" + raw, 10);
                            declare(name, stateSort);
                            containerStates.put(name, stateSort);
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
            public boolean preserveContainerIdentity(JsonElement expression,
                                                     ContainerSmtCodec.Sort expected) {
                return ContainerSmtCodec
                        .evidencedContainerIdentity(expression);
            }

            @Override
            public ContainerSmtCodec.Term operand(JsonElement expression,
                                                  ContainerSmtCodec.Sort expected) {
                if (ContainerSmtCodec.handles(expression)) {
                    return ContainerSmtCodec.term(
                            expression.getAsJsonObject(), this);
                }
                if (ContainerSmtCodec.handlesField(expression)) {
                    return ContainerSmtCodec.field(
                            expression.getAsJsonObject(), this);
                }
                return box(dispatch(expression,
                        VmTermLowering.sortOfContainer(expected),
                        origin + ":container-operand"));
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
                return new ContainerSmtCodec.Term(boxed,
                        ContainerSmtCodec.Sort.VALUE);
            }

            private ContainerSmtCodec.Term box(Term value) {
                return value == null ? null : new ContainerSmtCodec.Term(
                        value.text,
                        VmTermLowering.containerSortOf(value.sort));
            }

            @Override
            public ContainerSmtCodec.Term unbox(ContainerSmtCodec.Term value,
                                                String javaType) {
                return ContainerSmtCodec.unboxValue(value, javaType,
                        VmTermLowering.unboxedCellSort(
                                JavaSmtSorts.sortOfJava(javaType)), this);
            }

            @Override
            public void noteAbsentKeyDefault(String keyTerm,
                                             String absentCondition) {
                if (keyTerm == null || keyTerm.isEmpty()
                        || absentCondition == null
                        || absentCondition.isEmpty()) {
                    return;
                }
                String identity = keyTerm + "\u0000" + absentCondition;
                if (absentKeyDefaults.containsKey(identity)) return;
                String name = symbols.mint("absent_key_default__",
                        identity, 16);
                declare(name, Sort.BOOL);
                assertions.add("(assert (= " + name + " "
                        + absentCondition + "))");
                JsonObject row = new JsonObject();
                row.addProperty("solverTerm", name);
                row.addProperty("keyTerm", keyTerm);
                row.addProperty("origin", origin);
                absentKeyDefaults.put(identity, row);
            }

            @Override
            public void require(String predicate) {
                if (predicate == null || predicate.isEmpty()
                        || "true".equals(predicate)) {
                    return;
                }
                if (pathSideConditions != null) {
                    if (!pathSideConditions.contains(predicate)) {
                        pathSideConditions.add(predicate);
                    }
                } else if (assertedOnce.add(predicate)) {
                    assertions.add("(assert " + predicate + ")");
                }
            }

            @Override
            public ContainerSmtCodec.Term field(ContainerSmtCodec.Term owner,
                                                String ownerClass,
                                                int fieldOffset,
                                                String javaType) {
                Sort result = JavaSmtSorts.sortOfJava(javaType);
                if (owner == null
                        || owner.sort != ContainerSmtCodec.Sort.REF
                        || fieldOffset < 0 || result == Sort.UNKNOWN
                        || result.containerState()) {
                    unsupported("FieldAccessExpression:" + ownerClass + "@"
                            + fieldOffset + ":" + javaType);
                    return null;
                }
                String identity = ownerClass + "#" + fieldOffset + "#"
                        + javaType;
                String function = symbols.mint("field__", identity, 10);
                functions.put(function,
                        "(declare-fun " + function + " (Ref) "
                                + result.smt + ")");
                return new ContainerSmtCodec.Term(
                        "(" + function + " " + owner.text + ")",
                        VmTermLowering.containerSortOf(result));
            }

            @Override
            public void unsupported(String reason) {
                refuse(reason, "");
            }
        };
    }

    private static String boxed(Term value, String javaType) {
        String integral = ContainerSmtCodec.boxIntegral(value.text,
                javaType);
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

    // ------------------------------------------------------------------
    // The query.
    // ------------------------------------------------------------------

    /** Declares one name once; a second, different sort is a defect. */
    void declare(String name, Sort sort) {
        Sort held = declarations.putIfAbsent(name, sort);
        if (held != null && held != sort) {
            throw new IllegalStateException("SMT name " + name
                    + " declared as " + held + " and " + sort);
        }
    }

    /**
     * One fresh unconstrained value, for a construct this refused.
     *
     * <p>A refusal is already a gap, and a gap already refuses the
     * composition; the term exists so that lowering can carry on and name
     * every other gap in one pass rather than stopping at the first.  It is
     * free rather than a default literal, because a default would read as
     * something the execution produced.</p>
     */
    private Term free(Sort sort) {
        Sort declared = sort == null || sort == Sort.UNKNOWN
                ? Sort.VALUE : sort;
        String name = symbols.mint("unsupported__",
                pathScope + "#" + declared + "#" + unsupported.size(), 10);
        declare(name, declared);
        return Term.of(name, declared, declared == Sort.INT
                ? IntegralWidth.JAVA_INT : IntegralWidth.NONE);
    }

    /** Opens one path: its side conditions belong to it alone. */
    void beginPath(String scope) {
        pathSideConditions = new ArrayList<>();
        pathScope = scope == null ? "" : scope;
    }

    /** Closes it, answering the side conditions its lowering raised. */
    List<String> endPath() {
        List<String> conditions = pathSideConditions == null
                ? Collections.<String>emptyList() : pathSideConditions;
        pathSideConditions = null;
        pathScope = "";
        return conditions;
    }

    Map<String, String> opaqueIdentities() {
        return opaqueIdentities;
    }

    /** Lowers one boolean constraint, with its Java definedness. */
    String condition(JsonElement expression, String origin) {
        Term term = dispatch(expression, Sort.BOOL, origin);
        if (term == null || term.sort != Sort.BOOL) {
            refuse(origin + ":NON_BOOLEAN_CONSTRAINT", "");
            return "true";
        }
        return and(Arrays.asList(term.precondition, term.text));
    }

    void assertNamed(String name, String formula) {
        assertions.add("(assert (! " + formula + " :named " + name + "))");
    }

    void assertPlain(String formula) {
        assertions.add("(assert " + formula + ")");
    }

    Set<String> unsupported() {
        return unsupported;
    }

    Map<String, String> unsupportedDetail() {
        return unsupportedDetail;
    }

    Set<String> cuts() {
        return cuts;
    }

    Map<String, String> rootTerms() {
        return rootTerms;
    }

    /** One row per associative read that answered out of the default. */
    Collection<JsonObject> absentKeyDefaults() {
        return absentKeyDefaults.values();
    }

    /** The whole query: preamble, declarations, assertions, check-sat. */
    String render() {
        StringBuilder query = new StringBuilder();
        query.append("; GraphChecker path-merge composed query").append('\n');
        query.append("(set-logic ALL)").append('\n');
        query.append("(set-option :produce-models true)").append('\n');
        for (String line : VmTermLowering.preamble(false)) {
            query.append(line).append('\n');
        }
        query.append(VmTermLowering.JAVA_INT_TO_STRING).append('\n');
        query.append(JavaPrimitiveSmtSemantics.INT_WRAP_DEFINITION)
                .append('\n');
        query.append(JavaPrimitiveSmtSemantics.LONG_WRAP_DEFINITION)
                .append('\n');
        for (String declaration : functions.values()) {
            query.append(declaration).append('\n');
        }
        for (Map.Entry<String, Sort> declaration : declarations.entrySet()) {
            query.append("(declare-const ").append(declaration.getKey())
                    .append(' ').append(declaration.getValue().smt)
                    .append(")").append('\n');
        }
        for (String assertion : assertions) {
            query.append(assertion).append('\n');
        }
        query.append("(check-sat)").append('\n');
        return query.toString();
    }

    /** Named rows of the rendered query, the formula-size measure. */
    int namedRows() {
        return declarations.size() + functions.size() + assertions.size();
    }
}
