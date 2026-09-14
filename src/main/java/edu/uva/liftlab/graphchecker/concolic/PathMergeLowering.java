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

    /** Every instant each clock root was read at, by solver term. */
    private final Map<String, Set<String>> clockReadings =
            new LinkedHashMap<>();
    /** The one refusal that means "propagation did not carry the value". */
    static final String CUT = "PROPAGATION_CUT";

    private final SmtSymbolTable symbols = new SmtSymbolTable();
    private final Map<String, Sort> declarations = new LinkedHashMap<>();
    private final List<String> assertions = new ArrayList<>();
    private final Set<String> assertedOnce = new LinkedHashSet<>();
    /** Raw VM symbol -> the root inventory row that declares it. */
    private final Map<String, JsonObject> declaredRoots;
    /** Solver term -> the raw VM symbol it stands for. */
    private final Map<String, String> rootTerms = new LinkedHashMap<>();
    /** Raw VM symbol -> the one solver name that root is lowered to. */
    private final Map<String, String> rootNames = new LinkedHashMap<>();
    /** Solver term -> the execution-local identity it stands for. */
    private final Map<String, String> opaqueIdentities =
            new LinkedHashMap<>();
    /** Replay scope -> the objects it held, by the rid the VM gave them. */
    private final Map<String, Map<Long, String>> recordedObjects =
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
    /** Container subterms named once, in the order they were built. */
    private final Map<String, SharedTerm> sharedTerms =
            new LinkedHashMap<>();
    private List<String> pathRefusals;
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
    private final Set<String> integralDomains = new LinkedHashSet<>();
    private boolean usesJavaIntString;

    PathMergeLowering(Map<String, JsonObject> declaredRoots) {
        this.declaredRoots = declaredRoots == null
                ? Collections.<String, JsonObject>emptyMap() : declaredRoots;
        Map<String, List<String>> byDeclaredName = new LinkedHashMap<>();
        for (Map.Entry<String, JsonObject> declared
                : this.declaredRoots.entrySet()) {
            byDeclaredName.computeIfAbsent(
                    declaredRootName(declared.getValue(), declared.getKey()),
                    ignored -> new ArrayList<String>())
                    .add(declared.getKey());
        }
        for (Map.Entry<String, List<String>> shared
                : byDeclaredName.entrySet()) {
            for (String raw : shared.getValue()) {
                rootNames.put(raw, shared.getValue().size() == 1
                        ? shared.getKey()
                        : symbols.mint(shared.getKey() + "__", raw, 10));
            }
        }
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

    /**
     * One container subterm, lowered once and referenced by name.
     *
     * <p>A container version is read by every condition that mentions it,
     * and its chain is the whole mutation history.  Re-inlining it at each
     * read grows the formula as the product of the two, which is how one
     * 17897 target reached OutOfMemoryError inside the unboxing of a chain
     * element.  Naming it costs one {@code define-fun} and changes nothing
     * the formula means.</p>
     */
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
     * <p>Interned by digest of sort and text, so one version lowered twice
     * is one definition.  Insertion order is a topological order because a
     * term is named only after the terms it is built from.</p>
     */
    private ContainerSmtCodec.Term name(ContainerSmtCodec.Term value) {
        if (value == null || value.text.isEmpty()
                || value.text.charAt(0) != '(') {
            return value;
        }
        Sort sort = VmTermLowering.sortOfContainer(value.sort);
        if (sort == Sort.UNKNOWN) return value;
        String identity = sort.name() + "\u0000" + value.text;
        String digest = CanonicalJson.sha256(identity);
        SharedTerm held = sharedTerms.get(digest);
        if (held == null) {
            held = new SharedTerm(symbols.mint("container_dag__", identity,
                    24), sort, value.text);
            sharedTerms.put(digest, held);
        }
        return new ContainerSmtCodec.Term(held.name, value.sort,
                value.integralWidth);
    }

    /**
     * Conjoins one fact into the path being lowered, or the query.
     *
     * <p>A fact a path's own lowering raised is true where that path ran
     * and nowhere else, so while a path is open it goes into that path's
     * conjunction; between paths there is one query to state it in.</p>
     */
    private void sideCondition(String predicate) {
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

    /**
     * What a joined read observed, conjoined into the path that read it.
     *
     * <p>A projection the resolver joined is the writer's own expression,
     * not a value, and that is what makes the chain from a root to this
     * read one formula.  The recording also states what the read returned,
     * and that fact is this path's own control exactly as the value it read
     * at a handoff is: the path is admitted only where its replay's own
     * valuation satisfies it.  Stating it is therefore a conjunct of the
     * path, never a pin on the expression -- the expression stays free to
     * take other values under other paths' arms.</p>
     */
    @Override
    void recordedReading(Term value, JsonElement observed, String origin) {
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

    /** Records one refusal; a cut is the subset the gate reads. */
    private void refuse(String subject, String detail) {
        unsupported.add(subject);
        if (pathRefusals != null) pathRefusals.add(subject);
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
        Sort sort;
        sort = expected == Sort.MAP || expected == Sort.ARRAY_VALUE
                ? expected
                : encoded != Sort.VALUE ? encoded
                : expected == null ? Sort.REF : expected;
        JsonObject root = declaredRoots.get(raw);
        // One variable has one sort.  The declaration states the Java type
        // the runtime minted it at; the node it turned up in states only
        // what that site expected, and on laneVM12 the same handoff
        // variable appeared once where an int was expected and once where a
        // reference was, which z3 rejects as two declarations of one name.
        // The declaration wins, because it is the mint.
        if (root != null) {
            Sort declaredSort = JavaSmtSorts.sortOfJava(
                    optionalString(root, "javaType"));
            if (declaredSort != Sort.VALUE) sort = declaredSort;
        }
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
        String declaredType = firstNonBlank(
                optionalString(root, "javaType"), javaType);
        assertJavaIntegralDomain(name, sort, declaredType, raw);
        // A declared variable carries the width its Java type gives it.
        // Leaving every one at NONE made an int-typed handoff value mixed
        // with a long-typed term read as an ambiguous binary width, and a
        // long-typed one in an lcmp read as malformed operands: the
        // lowering had the type and threw it away one line before the
        // arithmetic that needed it.
        return Term.of(name, sort,
                JavaPrimitiveSmtSemantics.widthOfJavaType(declaredType),
                "", "", "true");
    }

    /**
     * One execution-local identity, named once, free but not nothing.
     *
     * <p>Which object an execution ran on says nothing about the failure, so
     * the identity is opaque.  Two things about it were recorded, though,
     * and stating them is not an assumption: the execution read fields off
     * the object, so it was not null; and two different rids in one replay
     * are two different objects.  Left unsaid, a model answers a null check
     * by making the reference null and a lookup by making two keys the same
     * object -- lane17897j's healthy path had both arms satisfiable at its
     * own recorded valuation for exactly that reason.</p>
     */
    private String opaque(String raw, Sort sort) {
        String name = symbols.mint("identity__",
                pathScope + "\0" + sort + "\0" + raw, 10);
        declare(name, sort);
        // Said once per identity: the mint answers with the same name every
        // time the same object is reached, and the fact is about the object.
        boolean minted = opaqueIdentities.put(name, raw) == null;
        long rid = InSessionReadResolver.referencedObjectRid(raw);
        if (minted && sort == Sort.REF && rid > 0L) {
            assertPlain("(not (= " + name + " nullRef))");
            Map<Long, String> held = recordedObjects.get(pathScope);
            if (held == null) {
                held = new LinkedHashMap<>();
                recordedObjects.put(pathScope, held);
            }
            held.put(rid, name);
        }
        return name;
    }

    /**
     * "Different rids, different objects", once per replay.
     *
     * <p>One assertion per scope rather than a pair per pair: the fact is
     * about the whole set, and z3 reads {@code distinct} that way.</p>
     */
    void assertRecordedObjectsDistinct() {
        for (Map<Long, String> held : recordedObjects.values()) {
            if (held.size() < 2) continue;
            assertPlain("(distinct " + String.join(" ", held.values()) + ")");
        }
    }

    /** The one solver name of one declared root. */
    String rootTerm(JsonObject root, String raw, Sort sort) {
        String name = rootName(root, raw);
        declare(name, sort);
        rootTerms.put(name, raw);
        return name;
    }

    /**
     * One name per ROOT, never per symbolization action.
     *
     * <p>A declared {@code symbol} is the port a planned symbolization
     * fires at, and one port mints a fresh root at every value it fires
     * on.  On hdfs-17899 bug1 one heartbeat's port carried three
     * {@code BlockKey} expiry dates -- RETIRED, CURRENT and the base --
     * as three raw symbols with three recorded values, so a path that
     * read them stated three values of one term and was refused
     * PATH_NOT_SELF_CONSISTENT at its own replay's valuation, naming one
     * of the three readings as the conjunct that closed it.  Where a
     * declared symbol names exactly one root it is the name; where it
     * names several, each root carries its own raw symbol's digest.</p>
     */
    String rootName(JsonObject root, String raw) {
        String name = rootNames.get(raw);
        return name == null ? declaredRootName(root, raw) : name;
    }

    private static String declaredRootName(JsonObject root, String raw) {
        return JavaSmtSorts.smtName(firstNonBlank(
                optionalString(root, "symbol"), "sym__" + raw));
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
            public ContainerSmtCodec.Term share(
                    ContainerSmtCodec.Term value) {
                return name(value);
            }

            @Override
            public ContainerSmtCodec.Term operand(JsonElement expression,
                                                  ContainerSmtCodec.Sort expected) {
                if (ContainerSmtCodec.handles(expression)) {
                    return name(ContainerSmtCodec.term(
                            expression.getAsJsonObject(), this));
                }
                if (ContainerSmtCodec.handlesField(expression)) {
                    return name(ContainerSmtCodec.field(
                            expression.getAsJsonObject(), this));
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
                return name(new ContainerSmtCodec.Term(boxed,
                        ContainerSmtCodec.Sort.VALUE));
            }

            private ContainerSmtCodec.Term box(Term value) {
                return value == null ? null : new ContainerSmtCodec.Term(
                        value.text,
                        VmTermLowering.containerSortOf(value.sort));
            }

            @Override
            public ContainerSmtCodec.Term unbox(ContainerSmtCodec.Term value,
                                                String javaType) {
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
        pathRefusals = new ArrayList<>();
        pathScope = scope == null ? "" : scope;
    }

    /**
     * What this path's own lowering refused.
     *
     * <p>The global set dedups by subject, so a second path that hits the
     * same refusal adds nothing to it and would read as clean.  A caller
     * deciding whether to admit THIS path needs its own list.</p>
     */
    List<String> pathRefusals() {
        return pathRefusals == null
                ? Collections.<String>emptyList() : pathRefusals;
    }

    /** Closes it, answering the side conditions its lowering raised. */
    List<String> endPath() {
        List<String> conditions = pathSideConditions == null
                ? Collections.<String>emptyList() : pathSideConditions;
        pathSideConditions = null;
        pathRefusals = null;
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

    /**
     * One instant a clock root was read at, by solver term.
     *
     * <p>A clock has no single domain -- each execution reads it fresh, and
     * a path is windowed around its own reading -- but it does have the set
     * of readings the recording states, and nothing outside their windows is
     * a clock any run of this case returned.  Collected here so the union
     * can be asserted once, for every clock root the query declares rather
     * than only for those an admitted path values.</p>
     */
    void observeClockReading(String term, String reading) {
        if (term == null || term.isEmpty()
                || reading == null || reading.isEmpty()) {
            return;
        }
        Set<String> readings = clockReadings.get(term);
        if (readings == null) {
            readings = new LinkedHashSet<>();
            clockReadings.put(term, readings);
        }
        readings.add(reading.trim());
    }

    /** Every instant one clock root was read at, in the order seen. */
    Set<String> clockReadings(String term) {
        Set<String> readings = clockReadings.get(term);
        return readings == null ? Collections.<String>emptySet() : readings;
    }

    /**
     * The union of the windows around every reading of each clock root: the
     * domain a clock root has whatever path values it.
     */
    List<String> clockDomains(long skewMillis) {
        List<String> domains = new ArrayList<>();
        for (Map.Entry<String, Set<String>> entry
                : clockReadings.entrySet()) {
            List<String> windows = new ArrayList<>();
            for (String reading : entry.getValue()) {
                try {
                    String window = ClockRootPhysics.window(entry.getKey(),
                            Long.parseLong(reading), skewMillis);
                    if (!window.isEmpty()) windows.add(window);
                } catch (NumberFormatException notAnInstant) {
                    // A reading that is not an instant states no window;
                    // the path that read it carries whatever it does.
                    return Collections.emptyList();
                }
            }
            if (windows.isEmpty()) continue;
            domains.add(windows.size() == 1 ? windows.get(0)
                    : "(or " + String.join(" ", windows) + ")");
        }
        return domains;
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


    /**
     * Preamble and declarations, with no assertion and no check.
     *
     * <p>What a caller needs to ask a question about one path on its own:
     * the sorts and the names, without the other paths' conjunctions.</p>
     */
    String declarationsOnly() {
        StringBuilder query = new StringBuilder();
        appendPreamble(query);
        return query.toString();
    }

    private void appendPreamble(StringBuilder query) {
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

    /** The whole query: preamble, declarations, assertions, check-sat. */
    String render() {
        StringBuilder query = new StringBuilder();
        appendPreamble(query);
        for (String assertion : assertions) {
            query.append(assertion).append('\n');
        }
        query.append("(check-sat)").append('\n');
        return query.toString();
    }

    /** Named rows of the rendered query, the formula-size measure. */
    int namedRows() {
        return declarations.size()
                + sharedTerms.size() + assertions.size();
    }
}
