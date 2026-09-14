package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.IntegralWidth;
import edu.uva.liftlab.graphchecker.concolic.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.concolic.VmTermLowering.Term;
import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.FloatingKind;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sha256;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.VmTermLowering.floatingKind;
import static edu.uva.liftlab.graphchecker.concolic.VmTermLowering.numeric;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.requiredObject;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.arithmetic;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.arithmeticOperator;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.bitwiseOperator;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.comparison;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.constantPayload;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.exactIntLiteral;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.flattenConcat;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.isJavaParseInt;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.isJavaSplitElement;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.isPrimitiveIntExpression;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.quote;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.shiftOperator;

/** Solves one canonical path flip and maps its model to real input actions. */
public final class ConcolicConstraintSolver {
    private ConcolicConstraintSolver() {
    }

    /** Solves one primary flip against all materialization roots in its
     * linked causal replay bundle. */
    static Result solve(JsonObject task, List<JsonObject> linkedActivations,
                        JsonObject primaryActivation, Path z3,
                        long timeoutMillis)
            throws IOException, InterruptedException {
        LinkedActivation linked = linkedActivation(linkedActivations,
                primaryActivation);
        JsonObject activation = linked.inputs;
        PathQuery query = PathQuery.decode(task);
        BranchReplayContract replayContract = query.replayContract;
        // The obligation's path condition as the replay it was cut from
        // valued it: roots, literals and containers over them, and no
        // placeholder for this solver to choose a value for.  The planner
        // resolved it, because only there does that replay still have its
        // rows.
        JsonObject resolved = ResolvedFlipQuery.of(task);
        JsonArray unresolvedReasons = resolved == null
                ? new JsonArray() : array(resolved, "unresolved");
        JsonArray branchConstraints = resolved == null
                ? replayContract.requiredPathPredicates()
                : array(resolved, "predicates");
        JsonArray contextConstraints = resolved == null
                ? query.pathContext.expressions()
                : array(resolved, "context");
        if (unresolvedReasons.size() > 0) {
            JsonObject cut = baseRecord(query.queryKey);
            cut.add("unsupported", new JsonArray());
            cut.addProperty("status", "MATERIALIZATION_GAP");
            cut.addProperty("reason", ResolvedFlipQuery.UNRESOLVED_REASON);
            cut.add("unresolvedPathCondition", unresolvedReasons.deepCopy());
            return new Result(cut, "", new JsonArray(), replayContract);
        }
        List<JsonObject> actions = materializationActions(activation);
        Encoder encoder = new Encoder();
        for (int index = 0; index < contextConstraints.size(); index++) {
            JsonElement constraint = contextConstraints.get(index);
            encoder.addConstraint(constraint, "q_context_" + index);
        }
        // The replay-control frontier is the union of the branch
        // predicates, not of every semantic support expression they rest on.
        Set<String> replayFrontier = new LinkedHashSet<>();
        Set<String> targetSymbols = new LinkedHashSet<>();
        for (int index = 0; index < branchConstraints.size(); index++) {
            boolean target = index + 1 == branchConstraints.size();
            Set<String> symbols = encoder.addConstraint(
                    branchConstraints.get(index), "q_branch_" + index);
            replayFrontier.addAll(symbols);
            if (target) {
                targetSymbols.addAll(symbols);
            }
        }
        ReplaySupport targetSupport = classifyReplaySupport(
                encoder, targetSymbols, actions,
                linked.configuredSourcePhaseCatalogs);
        ReplaySupport replaySupport = classifyReplaySupport(
                encoder, replayFrontier, actions,
                linked.configuredSourcePhaseCatalogs);
        Set<String> writableReplayControlSymbols =
                replaySupport.writableSymbols;
        preferObservedReplayControls(encoder,
                writableReplayControlSymbols, actions);
        String smt = encoder.finish();
        JsonObject record = baseRecord(query.queryKey);
        record.add("unsupported", strings(encoder.unsupported));
        if (!encoder.unsupported.isEmpty()) {
            record.addProperty("status", "UNSUPPORTED");
            record.addProperty("reason", "UNSUPPORTED_EXPRESSION_IR");
            return new Result(record, smt, new JsonArray(),
                    replayContract);
        }

        if (!targetSupport.unresolvedSymbols.isEmpty()) {
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason",
                    "FLIP_CONDITION_DEPENDS_ON_UNMATERIALIZABLE_SYMBOLS");
            record.add("unresolvedTargetSymbols",
                    strings(targetSupport.unresolvedSymbols));
            return new Result(record, smt, new JsonArray(),
                    replayContract);
        }

        if (!replaySupport.unresolvedSymbols.isEmpty()) {
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason",
                    "REPLAY_CONTROL_FRONTIER_IS_NOT_MATERIALIZABLE");
            record.add("unresolvedReplaySupportSymbols",
                    strings(replaySupport.unresolvedSymbols));
            return new Result(record, smt, new JsonArray(),
                    replayContract);
        }

        Path executable = z3 == null ? Paths.get("z3") : z3;
        SolverOutput output = run(executable, smt,
                Math.max(1L, timeoutMillis));
        if (output.timedOut) {
            record.addProperty("status", "SOLVER_ERROR");
            record.addProperty("reason", "SOLVER_TIMEOUT");
            return new Result(record, smt, new JsonArray(),
                    replayContract);
        }
        String status = output.status();
        if ("unsat".equals(status)) {
            record.addProperty("status", "UNSAT");
            return new Result(record, smt, new JsonArray(),
                    replayContract);
        }
        if (!"sat".equals(status)) {
            record.addProperty("status", "SOLVER_ERROR");
            record.addProperty("reason", firstNonBlank(status,
                    "NO_SOLVER_STATUS"));
            return new Result(record, smt, new JsonArray(),
                    replayContract);
        }

        Map<String, String> values = parseGetValues(output.stdout);
        Set<String> projectedSymbols = new LinkedHashSet<>(
                writableReplayControlSymbols);
        ModelProjection projection = modelAssignments(encoder, values,
                actions, linked.configuredSourcePhaseCatalogs,
                projectedSymbols);
        JsonArray assignments = projection.assignments;
        if (projectedSymbols.isEmpty()) {
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason", "NO_REGION_INPUT_SYMBOL_IN_QUERY");
        } else if (!projection.unresolved.isEmpty()) {
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason",
                    "REPLAY_CONTROL_FRONTIER_MODEL_IS_NOT_MATERIALIZABLE");
            record.add("unresolvedReplayControlSymbols",
                    strings(projection.unresolved));
        } else {
            record.addProperty("status", "SAT_MODEL_READY");
        }
        return new Result(record, smt, assignments, replayContract);
    }

    /** One solver view over the input authorities of a linked replay plan. */
    private static LinkedActivation linkedActivation(
            List<JsonObject> activations, JsonObject primary)
            throws IOException {
        if (primary == null) {
            throw new IOException("linked replay has no primary activation");
        }
        JsonObject result = primary.deepCopy();
        Map<String, JsonObject> actions = new LinkedHashMap<>();
        List<List<ConfiguredSourcePhaseContract.Occurrence>> phaseCatalogs =
                new ArrayList<>();
        for (JsonObject activation : activations == null
                ? Collections.<JsonObject>emptyList() : activations) {
            final InputActionCatalog catalog;
            try {
                catalog = InputActionCatalog.decode(activation);
            } catch (IllegalArgumentException malformed) {
                throw new IOException("invalid linked input actions: "
                        + malformed.getMessage(), malformed);
            }
            for (JsonElement element : catalog.all()) {
                JsonObject action = element.getAsJsonObject().deepCopy();
                String key = optionalString(action, "symbol") + "\n"
                        + CanonicalJson.render(action);
                actions.putIfAbsent(key, action);
            }
            try {
                List<ConfiguredSourcePhaseContract.Occurrence> phases =
                        ConfiguredSourcePhaseContract.occurrencesOf(
                                activation.get(ConfiguredSourcePhaseContract
                                        .PLAN_FIELD));
                if (!phases.isEmpty()) phaseCatalogs.add(phases);
            } catch (IllegalArgumentException malformed) {
                throw new IOException("invalid linked configured source "
                        + "phases: " + malformed.getMessage(), malformed);
            }
        }
        JsonArray encodedActions = new JsonArray();
        for (JsonObject action : actions.values()) encodedActions.add(action);
        result.add(InputActionCatalog.FIELD, encodedActions);
        result.remove(ConfiguredSourcePhaseContract.PLAN_FIELD);
        return new LinkedActivation(result, phaseCatalogs);
    }

    /** Input actions may be unioned, but ordered source-phase catalogs may
     * only be validated inside the activation that owns their ordinals. */
    private static final class LinkedActivation {
        private final JsonObject inputs;
        private final List<List<ConfiguredSourcePhaseContract.Occurrence>>
                configuredSourcePhaseCatalogs;
        private LinkedActivation(JsonObject inputs,
                List<List<ConfiguredSourcePhaseContract.Occurrence>> catalogs) {
            this.inputs = inputs;
            this.configuredSourcePhaseCatalogs = catalogs;
        }
    }

    private static final class ReplaySupport {
        private final Set<String> writableSymbols;
        private final Set<String> unresolvedSymbols;

        private ReplaySupport(Set<String> writableSymbols,
                              Set<String> unresolvedSymbols) {
            this.writableSymbols = writableSymbols;
            this.unresolvedSymbols = unresolvedSymbols;
        }
    }

    private static final class ModelProjection {
        private final JsonArray assignments;
        private final Set<String> unresolved;

        private ModelProjection(JsonArray assignments,
                                Set<String> unresolved) {
            this.assignments = assignments;
            this.unresolved = unresolved;
        }
    }

    public static final class Result {
        public final JsonObject record;
        public final String smtLib;
        public final JsonArray modelAssignments;
        final BranchReplayContract replayContract;

        private Result(JsonObject record, String smtLib,
                       JsonArray modelAssignments,
                       BranchReplayContract replayContract) {
            this.record = record;
            this.smtLib = smtLib;
            this.modelAssignments = modelAssignments;
            this.replayContract = replayContract;
        }
    }

    private static final class Encoder extends VmLoweringCore {
        private static final String SHARED_TERM_PREFIX = "container_dag__";
        private final SmtSymbolTable smtSymbols = new SmtSymbolTable();
        private final Map<String, Sort> declarations = new LinkedHashMap<>();
        private final Map<String, String> functionDeclarations =
                new LinkedHashMap<>();
        private final Map<String, SymbolNames> names =
                new LinkedHashMap<>();
        private final Map<String, String> containerStates =
                new LinkedHashMap<>();
        /** Bottom-up pure aliases for repeated propagated subterms. */
        private final Map<String, SharedTermDefinition> sharedTerms =
                new LinkedHashMap<>();
        /** Exact duplicate predicates add no semantics and burden Z3's
         * command-by-command simplifier, so retain only their first order. */
        private final Set<String> assertions = new LinkedHashSet<>();
        /** Model-only preferences: they choose a stable replay without
         * changing whether the hard path query is reachable. */
        private final Set<String> softAssertions = new LinkedHashSet<>();
        private final Set<String> unsupported = new LinkedHashSet<>();
        private final Set<String> controlledSymbols = new LinkedHashSet<>();
        private final Set<String> javaIntRangeAssertions =
                new LinkedHashSet<>();
        private boolean usesJavaIntString;
        private Set<String> currentConstraintSymbols;

        // The shared lowering's policies.
        @Override
        public Term lower(JsonElement expression, Sort expected,
                          String origin) {
            return term(expression, expected, origin);
        }

        @Override
        public Term refuse(VmTermLowering.Reason reason, String origin,
                           String detail, Sort sort) {
            unsupported.add(reason.solverSubject(origin, detail));
            return null;
        }

        /** The solver asserts definedness eagerly, so nothing is carried. */
        @Override
        public Term dependent(Term result, Term... inputs) {
            return result;
        }

        @Override
        public Sort castSort(String descriptor) {
            return sortOfJava(descriptor);
        }

        @Override
        Sort sortOfJavaType(String javaType) {
            return sortOfJava(javaType);
        }

        /**
         * A flip query is one path's conjunction, so every operand on it is
         * evaluated: its definedness is stated outright rather than carried
         * on the term the way final composition carries it.
         */
        @Override
        Term definedResult(String text, Sort sort, IntegralWidth width,
                           String definedness, Term... inputs) {
            if (!"true".equals(definedness)) assertions.add(definedness);
            return Term.vm(text, sort, width);
        }

        /**
         * Every term here carries the definedness "true", so a short
         * circuit has no operand obligation to guard and states nothing.
         */
        @Override
        Term shortCircuit(String text, Term left, Term right,
                          boolean conjunction) {
            return Term.vm(text, Sort.BOOL);
        }

        /**
         * Evaluation of an instance String operation proves its receiver was
         * non-null, so the query may assert it; unknown nullability refuses.
         */
        @Override
        String stringDefinedness(String origin, String operation,
                                 List<Term> dereferenced,
                                 List<Term> evaluated) {
            for (int index = 0; index < dereferenced.size(); index++) {
                Term value = dereferenced.get(index);
                if (value == null || value.stringNullness.isEmpty()) {
                    unsupported.add(origin + ":STRING_"
                            + operation.toUpperCase(java.util.Locale.ROOT)
                            + "_NULLABILITY_UNKNOWN:" + index);
                    return null;
                }
                if (!"false".equals(value.stringNullness)) {
                    assertions.add(
                            "(not " + value.stringNullness + ")");
                }
            }
            return "true";
        }

        @Override
        void assertJavaIntegralDomain(String term, Sort sort,
                                      String javaType, String identity) {
            if (sort != Sort.INT) return;
            JavaPrimitiveSmtSemantics.IntegralDomain domain =
                    JavaPrimitiveSmtSemantics.domainOfJavaType(javaType);
            if (domain == null || term == null || term.isEmpty()) return;
            assertions.add(VmTermLowering.integralRange(domain.lower, term,
                    domain.upper));
        }

        @Override
        void noteJavaIntToString() {
            usesJavaIntString = true;
        }

        /** One recorded String.split prefix the codec could not close. */
        private Term splitElementGap(String gap) {
            return VmTermLowering.codecGap(this,
                    "java/lang/String.splitElement", gap, "", null);
        }

        @Override
        public VmTermLowering.RenderedInteger renderedInteger(
                JsonElement element, String origin) {
            SplitPrefix match = exactSplitPrefix(element);
            if (!match.complete()) {
                return new VmTermLowering.RenderedInteger(null,
                        "ROUNDTRIP_NOT_PROVED_" + match.gap);
            }
            return new VmTermLowering.RenderedInteger(term(
                    match.integerExpression, Sort.INT, origin + ":parseInt"),
                    "");
        }

        private Encoder() {
        }

        private Set<String> addConstraint(
                JsonElement expression, String origin) {
            currentConstraintSymbols = new LinkedHashSet<>();
            if (expression == null || !expression.isJsonObject()) {
                unsupported.add(origin + ":NON_OBJECT_EXPRESSION");
            } else {
                JsonObject object = expression.getAsJsonObject();
                String type = optionalString(object, "_type");
                if ("MethodExpression".equals(type)) {
                    String constraint = methodConstraint(object, origin);
                    if (!constraint.isEmpty()) assertions.add(constraint);
                } else {
                    Term term = term(expression, null, origin);
                    if (term != null && term.sort == Sort.BOOL) {
                        assertions.add(term.text);
                    } else if (term != null) {
                        unsupported.add(origin
                                + ":NON_BOOLEAN_CONSTRAINT");
                    }
                }
            }
            Set<String> result = currentConstraintSymbols;
            currentConstraintSymbols = null;
            return result;
        }

        private Term term(JsonElement expression, Sort expected,
                          String origin) {
            return dispatch(expression, expected, origin);
        }

        @Override
        Term symbolTerm(JsonObject expression, Sort expected,
                        String origin) {
            return symbol(expression, origin);
        }

        @Override
        Term placeholderTerm(JsonObject expression, String origin) {
            return placeholder(expression, origin);
        }

        @Override
        Term caseMergeTerm(JsonObject expression, Sort expected,
                           String origin) {
            // A value merged over another region's cases is a cross-replay
            // object.  One obligation is one replay's path condition.
            unsupported.add(origin + ":CASE_MERGE_IN_PATH:"
                    + optionalString(expression, "mergeId"));
            return null;
        }

        /** A refused call yields no term, so no sort is needed for it. */
        @Override
        Sort methodResultSort(JsonObject expression, String origin) {
            return null;
        }


        /** Lowers the VM's read-time candidate snapshot directly. */
        @Override
        Term guardedReadTerm(JsonObject read, Sort expected,
                             String origin) {
            // Every expression reaching this encoder was resolved inside its
            // own replay, so a surviving read is a value that replay did not
            // determine.  Choosing one here would be the solver inventing the
            // history the flip is supposed to test.
            unsupported.add(origin + ":UNRESOLVED_SHARED_READ:"
                    + InSessionReadResolver.sessionLocation(
                            object(read, "location")));
            return null;
        }



        @Override
        Term containerTerm(JsonObject expression, boolean field,
                           String origin) {
            if (field) {
                return fromContainerTerm(ContainerSmtCodec.field(
                        expression, containerHost(origin)), origin);
            }
            return fromContainerTerm(ContainerSmtCodec.term(
                    expression, containerHost(origin)), origin);
        }

        private ContainerSmtCodec.Host containerHost(final String origin) {
            return new ContainerSmtCodec.Host() {
                @Override
                public ContainerSmtCodec.Term state(
                        JsonElement identity,
                        ContainerSmtCodec.Sort shape) {
                    Sort stateSort = shape == ContainerSmtCodec.Sort.INDEXED
                            ? Sort.ARRAY_VALUE : Sort.MAP;
                    if (identity != null && identity.isJsonObject()
                            && "SymbolExpression".equals(optionalString(
                            identity.getAsJsonObject(), "_type"))) {
                        String raw = optionalString(identity.getAsJsonObject(), "_exp");
                        if (raw.isEmpty()) {
                            unsupported("ContainerStateIdentity:" + shape);
                            return null;
                        }
                        String key = shape + "\u0000" + raw;
                        String name = containerStates.get(key);
                        if (name == null) {
                            name = smtSymbols.mint("container__"
                                    + safeName(raw) + "__", key, 10);
                            containerStates.put(key, name);
                            declarations.put(name, stateSort);
                        }
                        return new ContainerSmtCodec.Term(name, shape);
                    }
                    Term reference = term(identity, Sort.REF,
                            origin + ":container-state");
                    if (reference == null || reference.sort != Sort.REF) {
                        unsupported("ContainerStateIdentity:" + shape);
                        return null;
                    }
                    return stateOfReference(reference.text, shape);
                }

                @Override
                public boolean preserveContainerIdentity(
                        JsonElement expression,
                        ContainerSmtCodec.Sort expected) {
                    return ContainerSmtCodec
                            .evidencedContainerIdentity(expression);
                }

                @Override
                public ContainerSmtCodec.Term operand(
                        JsonElement expression,
                        ContainerSmtCodec.Sort expected) {
                    if (ContainerSmtCodec.handles(expression)) {
                        JsonObject relation = expression.getAsJsonObject();
                        return ContainerSmtCodec.term(relation, this);
                    }
                    if (ContainerSmtCodec.handlesField(expression)) {
                        return shareTerm(ContainerSmtCodec.field(
                                expression.getAsJsonObject(), this));
                    }
                    return shareTerm(toContainerTerm(term(expression,
                            nativeSortOf(expected),
                            origin + ":container-operand")));
                }

                @Override
                public ContainerSmtCodec.Term share(
                        ContainerSmtCodec.Term value) {
                    return shareTerm(value);
                }

                @Override
                public ContainerSmtCodec.Term box(JsonElement expression) {
                    Term value = term(expression, null,
                            origin + ":container-value");
                    if (value == null) return null;
                    // A String box reads its nullness companion, so it is
                    // spelled out; every other value goes in as its alias.
                    String valueText = value.text;
                    if (value.sort != Sort.STRING) {
                        ContainerSmtCodec.Term shared = shareTerm(
                                toContainerTerm(value));
                        if (shared != null) valueText = shared.text;
                    }
                    Term boxed = asValue(value,
                            VmTermLowering.expressionJavaType(expression),
                            valueText, origin);
                    return boxed == null ? null
                            : shareTerm(toContainerTerm(boxed));
                }

                @Override
                public ContainerSmtCodec.Term unbox(
                        ContainerSmtCodec.Term value,
                        String javaType) {
                    return ContainerSmtCodec.unboxValue(value,
                            javaType, VmTermLowering.unboxedCellSort(sortOfJava(javaType)),
                            this);
                }

                @Override
                public void require(String predicate) {
                    assertions.add(predicate);
                }

                @Override
                public ContainerSmtCodec.Term field(
                        ContainerSmtCodec.Term owner, String ownerClass,
                        int fieldOffset, String javaType) {
                    Sort result = sortOfJava(javaType);
                    if (owner == null
                            || owner.sort != ContainerSmtCodec.Sort.REF
                            || fieldOffset < 0 || result == Sort.UNKNOWN
                            || result.containerState()) {
                        unsupported("FieldAccessExpression:" + ownerClass
                                + "@" + fieldOffset + ":" + javaType);
                        return null;
                    }
                    String identity = ownerClass + "\u0000" + fieldOffset
                            + "\u0000" + javaType;
                    String accessor = smtSymbols.mint(
                            "container_field__", identity, 16);
                    functionDeclarations.put(accessor,
                            "(declare-fun " + accessor + " (Ref) "
                                    + result.smt + ")");
                    return toContainerTerm(Term.vm("(" + accessor + " "
                            + owner.text + ")", result,
                            JavaPrimitiveSmtSemantics.widthOfJavaType(
                                    javaType)));
                }

                @Override
                public void unsupported(String reason) {
                    Encoder.this.unsupported.add(origin + ":" + reason);
                }
            };
        }

        /** The one codec-sort to solver-sort direction. */

        /**
         * Interns a compound codec term as a fully constrained constant.  A
         * zero-argument define-fun is a macro in Z3 and gets expanded again;
         * the equality keeps one shared AST while adding no semantic choice.
         * Exact text and sort form the alias identity.
         */
        private ContainerSmtCodec.Term shareTerm(
                ContainerSmtCodec.Term value) {
            if (value == null || value.text.isEmpty()
                    || value.text.charAt(0) != '(') {
                return value;
            }
            Sort sort = VmTermLowering.sortOfContainer(value.sort);
            if (sort == Sort.UNKNOWN) return value;
            String identity = sort.replayName() + "\u0000" + value.text;
            String digest = sha256(identity);
            SharedTermDefinition definition = sharedTerms.get(
                    digest);
            if (definition == null) {
                definition = new SharedTermDefinition(
                        smtSymbols.mintFromDigest(SHARED_TERM_PREFIX,
                                digest, identity, 24),
                        sort, value.text);
                sharedTerms.put(digest, definition);
            }
            return new ContainerSmtCodec.Term(definition.name, value.sort,
                    value.integralWidth);
        }

        private ContainerSmtCodec.Term toContainerTerm(Term value) {
            if (value == null) return null;
            ContainerSmtCodec.Sort sort =
                    VmTermLowering.containerSortOf(value.sort);
            return sort == null ? null
                    : new ContainerSmtCodec.Term(value.text, sort,
                    value.integralWidth);
        }

        private Term fromContainerTerm(
                ContainerSmtCodec.Term value, String origin) {
            if (value == null) return null;
            Sort sort = VmTermLowering.sortOfContainer(value.sort);
            if (sort == Sort.UNKNOWN) {
                unsupported.add(origin + ":CONTAINER_STATE_USED_AS_VALUE");
                return null;
            }
            return Term.vm(value.text, sort, value.integralWidth);
        }

        private Term symbol(JsonObject expression, String origin) {
            String raw = optionalString(expression, "_exp");
            if (VmExpressionIr.SYMBOLIC_NULL.equals(raw)) {
                return Term.vm("nullRef", Sort.REF);
            }
            if ("V".equals(raw)) return Term.vm("true", Sort.BOOL);
            if (currentConstraintSymbols != null && !raw.isEmpty()) {
                currentConstraintSymbols.add(raw);
            }
            String javaType = optionalString(expression, "_java_type");
            Sort sort = sortOfJava(javaType);
            if (raw.isEmpty() || sort == Sort.UNKNOWN) {
                unsupported.add(origin + ":UNSUPPORTED_SYMBOL_TYPE:"
                        + firstNonBlank(javaType, "MISSING"));
                return null;
            }
            IntegralWidth width = JavaPrimitiveSmtSemantics
                    .widthOfJavaType(javaType);
            SymbolNames symbolNames = names.get(raw);
            if (symbolNames == null) {
                symbolNames = new SymbolNames(raw, sort, width,
                        smtSymbols);
                names.put(raw, symbolNames);
            }
            String name = symbolNames.solver;
            if (!declarations.containsKey(name)) {
                declarations.put(name, sort);
                if (sort == Sort.STRING) {
                    declarations.put(symbolNames.nullness, Sort.BOOL);
                }
                if (regionInput(raw)) controlledSymbols.add(raw);
                constrainIntegralInput(name, javaType, sort);
                if (fixedNonNullReference(raw, sort)) {
                    assertions.add("(not (= " + name + " nullRef))");
                }
            } else {
                if (symbolNames.sort != sort) {
                    unsupported.add("SYMBOL_SORT_CONFLICT:" + raw + ":"
                            + symbolNames.sort + "->" + sort);
                }
                if (width != IntegralWidth.NONE
                        && symbolNames.width != IntegralWidth.NONE
                        && symbolNames.width != width) {
                    unsupported.add("SYMBOL_INTEGRAL_WIDTH_CONFLICT:" + raw
                            + ":" + symbolNames.width + "->" + width);
                }
            }
            if (symbolNames.sort == Sort.STRING) {
                return Term.vm(name, Sort.STRING, IntegralWidth.NONE,
                        symbolNames.nullness, raw);
            }
            return Term.vm(name, symbolNames.sort, symbolNames.width);
        }

        private SymbolNames names(String raw) {
            return names.get(raw);
        }


        private void constrainIntegralInput(String name,
                                            String javaType, Sort sort) {
            if (sort != Sort.INT) return;
            JavaPrimitiveSmtSemantics.IntegralDomain domain =
                    JavaPrimitiveSmtSemantics.domainOfJavaType(javaType);
            if (domain == null) return;
            assertions.add(VmTermLowering.integralRange(domain.lower,
                    name, domain.upper));
        }

        private Term placeholder(JsonObject expression, String origin) {
            String function = optionalString(expression, "_place_holder_func");
            int count = optionalInteger(expression, "_count", -1);
            if (!"currentTimeMills".equals(function) || count < 1) {
                unsupported.add(origin
                        + ":UNVERIFIED_PLACEHOLDER_EXPRESSION:"
                        + firstNonBlank(function, "MISSING_FUNCTION")
                        + "#" + count);
                return null;
            }
            String identity = function + "#" + count;
            if (currentConstraintSymbols != null) {
                // SolverPathContext records only this identity, not an exact
                // concrete value or provenance that would make it replay
                currentConstraintSymbols.add(
                        "ENVIRONMENT_PLACEHOLDER:" + identity);
            }
            String name = smtSymbols.mint("environment__"
                    + safeName(identity) + "__", identity, 10);
            declarations.put(name, Sort.INT);
            JavaPrimitiveSmtSemantics.IntegralDomain longDomain =
                    JavaPrimitiveSmtSemantics.domainOfJavaType("J");
            assertions.add("(and (<= " + longDomain.lower + " " + name
                    + ") (<= " + name + " " + longDomain.upper + "))");
            return Term.vm(name, Sort.INT, IntegralWidth.JAVA_LONG);
        }

        /** Lowers only casts whose value relation the SMT sorts preserve. */

        private String methodConstraint(JsonObject expression,
                                        String origin) {
            Term call = methodTerm(expression, origin);
            if (call == null) return "";
            Term result = term(expression.get("_res_exp"),
                    call.sort, origin + ":result");
            if (result == null) return "";
            if (call.sort != result.sort) {
                unsupported.add(origin + ":METHOD_RESULT_SORT_MISMATCH");
                return "";
            }
            return "(= " + result.text + " " + call.text + ")";
        }

        /** The composer's {@code parseIntTerm}, stated for this caller. */

        /** The composer's {@code splitElementTerm}, stated for this caller. */
        @Override
        Term splitElementTerm(JsonObject expression, String origin) {
            SplitPrefix match = exactSplitPrefix(expression);
            if (!match.complete()) {
                return splitElementGap(match.gap);
            }
            Term integer = term(match.integerExpression, Sort.INT,
                    origin + ":splitElement");
            if (integer == null || integer.sort != Sort.INT) {
                return splitElementGap("ROUNDTRIP_SOURCE_NOT_INT");
            }
            assertJavaIntRange(integer);
            return javaIntString(integer);
        }

        /**
         * The composer's {@code exactSplitPrefix}, for this caller.
         */
        private SplitPrefix exactSplitPrefix(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) {
                return SplitPrefix.gap("NOT_METHOD_EXPRESSION");
            }
            JsonObject split = expression.getAsJsonObject();
            if (!"MethodExpression".equals(optionalString(split, "_type"))
                    || !isJavaSplitElement(optionalString(split, "_name"))) {
                return SplitPrefix.gap("NOT_STRING_SPLIT_ELEMENT");
            }
            JsonArray params = array(split, "_param_list");
            if (params.size() != 3 && params.size() != 4) {
                return SplitPrefix.gap("SPLIT_ARITY");
            }
            Integer index = exactIntLiteral(params.get(params.size() - 1));
            if (index == null || index != 0) {
                return SplitPrefix.gap("INDEX_NOT_LITERAL_0");
            }
            String delimiter = VmExpressionIr.exactStringLiteral(
                    params.get(1), STRING_TYPED);
            String delimiterGap = delimiterGap(delimiter, true);
            if (!delimiterGap.isEmpty()) return SplitPrefix.gap(delimiterGap);
            if (params.size() == 4) {
                Integer limit = exactIntLiteral(params.get(2));
                // Java split(..., 1) returns the entire receiver and therefore
                // does not preserve the decimal prefix as element zero.  Zero,
                if (limit == null || limit == 1) {
                    return SplitPrefix.gap("LIMIT_DOES_NOT_PRESERVE_PREFIX");
                }
            }
            List<JsonElement> flattened = new ArrayList<>();
            if (!flattenConcat(params.get(0), flattened)) {
                return SplitPrefix.gap("CONCAT_PREFIX_AND_SUFFIX_REQUIRED");
            }
            // Concatenation commonly starts from the builder identity "".
            // Removing only exact empty literals is semantics-preserving;
            List<JsonElement> parts = new ArrayList<>();
            for (JsonElement part : flattened) {
                if (!"".equals(VmExpressionIr.exactStringLiteral(part,
                        STRING_TYPED))) parts.add(part);
            }
            if (parts.size() < 3) {
                return SplitPrefix.gap("CONCAT_PREFIX_AND_SUFFIX_REQUIRED");
            }
            JsonElement first = parts.get(0);
            if (first == null || !first.isJsonObject()) {
                return SplitPrefix.gap("PREFIX_NOT_INT_TO_STRING");
            }
            JsonObject toString = first.getAsJsonObject();
            JsonArray toStringParams = array(toString, "_param_list");
            if (!"OpStrExpression".equals(optionalString(toString, "_type"))
                    || !"toString".equals(optionalString(toString, "_name"))
                    || optionalBool(toString, "_is_not", false)
                    || toStringParams.size() != 1
                    || !isPrimitiveIntExpression(toStringParams.get(0))) {
                return SplitPrefix.gap("PREFIX_NOT_PRIMITIVE_INT_TO_STRING");
            }
            String concatenatedDelimiter = VmExpressionIr
                    .exactStringLiteral(parts.get(1), STRING_TYPED);
            if (concatenatedDelimiter == null
                    || !delimiter.equals(concatenatedDelimiter)) {
                return SplitPrefix.gap("SPLIT_CONCAT_DELIMITER_MISMATCH");
            }
            for (int indexOfSuffix = 2; indexOfSuffix < parts.size();
                 indexOfSuffix++) {
                if (!VmExpressionIr.provablyStringValued(
                        parts.get(indexOfSuffix), STRING_TYPED)) {
                    return SplitPrefix.gap("SUFFIX_NOT_STRING_VALUED");
                }
            }
            return SplitPrefix.complete(toStringParams.get(0));
        }

        @Override
        public void assertJavaIntRange(Term integer) {
            if (!javaIntRangeAssertions.add(integer.text)) return;
            assertions.add(VmTermLowering.javaIntRange(integer.text));
        }

        /** Emits only reachable shared terms and inlines one-use aliases. */
        private SharedTermEmission sharedTermEmission() {
            Map<String, SharedTermDefinition> definitions =
                    new LinkedHashMap<>();
            Map<String, Integer> order = new LinkedHashMap<>();
            int ordinal = 0;
            for (SharedTermDefinition definition : sharedTerms.values()) {
                definitions.put(definition.name, definition);
                order.put(definition.name, ordinal++);
            }
            Map<String, List<String>> dependencies = new LinkedHashMap<>();
            boolean topological = true;
            for (SharedTermDefinition definition : sharedTerms.values()) {
                List<String> names = new ArrayList<>();
                for (SharedAliasToken token
                        : sharedAliasTokens(definition.body)) {
                    names.add(token.name);
                }
                dependencies.put(definition.name, names);
                for (String name : names) {
                    Integer dependency = order.get(name);
                    if (dependency != null
                            && dependency >= order.get(definition.name)) {
                        topological = false;
                    }
                }
            }

            Set<String> reachable = new LinkedHashSet<>();
            List<String> pending = new ArrayList<>();
            for (String assertion : assertions) {
                for (SharedAliasToken token
                        : sharedAliasTokens(assertion)) {
                    String name = token.name;
                    if (definitions.containsKey(name)
                            && reachable.add(name)) pending.add(name);
                }
            }
            for (String declaration : functionDeclarations.values()) {
                for (SharedAliasToken token
                        : sharedAliasTokens(declaration)) {
                    String name = token.name;
                    if (definitions.containsKey(name)
                            && reachable.add(name)) pending.add(name);
                }
            }
            for (int index = 0; index < pending.size(); index++) {
                for (String name : dependencies.get(pending.get(index))) {
                    if (definitions.containsKey(name)
                            && reachable.add(name)) pending.add(name);
                }
            }

            Map<String, Integer> references = new LinkedHashMap<>();
            for (String assertion : assertions) {
                countSharedAliases(assertion, reachable, references);
            }
            for (String declaration : functionDeclarations.values()) {
                countSharedAliases(declaration, reachable, references);
            }
            for (SharedTermDefinition definition : sharedTerms.values()) {
                if (reachable.contains(definition.name)) {
                    countSharedAliases(definition.body, reachable,
                            references);
                }
            }
            Map<String, String> inline = new LinkedHashMap<>();
            List<SharedTermDefinition> emitted = new ArrayList<>();
            for (SharedTermDefinition definition : sharedTerms.values()) {
                if (!reachable.contains(definition.name)) continue;
                String body = replaceSharedAliases(definition.body, inline);
                if (topological
                        && Integer.valueOf(1).equals(
                        references.get(definition.name))) {
                    inline.put(definition.name, body);
                } else {
                    emitted.add(new SharedTermDefinition(definition.name,
                            definition.sort, body));
                }
            }
            List<String> roots = new ArrayList<>();
            for (String assertion : assertions) {
                roots.add(replaceSharedAliases(assertion, inline));
            }
            List<String> functions = new ArrayList<>();
            for (String declaration : functionDeclarations.values()) {
                functions.add(replaceSharedAliases(declaration, inline));
            }
            return new SharedTermEmission(emitted, functions, roots);
        }

        private static void countSharedAliases(String text,
                Set<String> reachable, Map<String, Integer> counts) {
            for (SharedAliasToken token : sharedAliasTokens(text)) {
                String name = token.name;
                if (reachable.contains(name)) {
                    counts.put(name, counts.getOrDefault(name, 0) + 1);
                }
            }
        }

        /** Finds exact, unquoted SMT symbols rather than substrings. */
        private static List<SharedAliasToken> sharedAliasTokens(String text) {
            List<SharedAliasToken> result = new ArrayList<>();
            int length = text.length();
            for (int index = 0; index < length;) {
                char current = text.charAt(index);
                if (Character.isWhitespace(current)
                        || current == '(' || current == ')') {
                    index++;
                    continue;
                }
                if (current == ';') {
                    int newline = text.indexOf('\n', index + 1);
                    index = newline < 0 ? length : newline + 1;
                    continue;
                }
                if (current == '"' || current == '|') {
                    index = quotedTokenEnd(text, index, current);
                    continue;
                }
                int start = index;
                while (index < length
                        && !Character.isWhitespace(text.charAt(index))
                        && text.charAt(index) != '('
                        && text.charAt(index) != ')'
                        && text.charAt(index) != ';') {
                    index++;
                }
                String token = text.substring(start, index);
                if (sharedAliasName(token)) {
                    result.add(new SharedAliasToken(token, start, index));
                }
            }
            return result;
        }

        private static int quotedTokenEnd(String text, int start,
                                           char quote) {
            int index = start + 1;
            while (index < text.length()) {
                char current = text.charAt(index++);
                if (current == '\\' && index < text.length()) {
                    index++;
                } else if (current == quote) {
                    if (quote == '"' && index < text.length()
                            && text.charAt(index) == '"') {
                        index++;
                    } else {
                        break;
                    }
                }
            }
            return index;
        }

        private static boolean sharedAliasName(String token) {
            if (token.length() != SHARED_TERM_PREFIX.length() + 24
                    || !token.startsWith(SHARED_TERM_PREFIX)) return false;
            for (int index = SHARED_TERM_PREFIX.length();
                 index < token.length(); index++) {
                char value = token.charAt(index);
                if (value < '0' || value > '9'
                        && (value < 'a' || value > 'f')) return false;
            }
            return true;
        }

        private static String replaceSharedAliases(
                String text, Map<String, String> replacements) {
            if (replacements.isEmpty()) return text;
            StringBuilder result = null;
            int copied = 0;
            for (SharedAliasToken token : sharedAliasTokens(text)) {
                String replacement = replacements.get(token.name);
                if (replacement != null) {
                    if (result == null) {
                        result = new StringBuilder(text.length());
                    }
                    result.append(text, copied, token.start)
                            .append(replacement);
                    copied = token.end;
                }
            }
            return result == null ? text
                    : result.append(text, copied, text.length()).toString();
        }

        private String finish() {
            SharedTermEmission shared = sharedTermEmission();
            StringBuilder result = new StringBuilder();
            result.append("(set-option :produce-models true)\n");
            result.append("(set-logic ALL)\n");
            for (String declaration : VmTermLowering.preamble(true)) {
                result.append(declaration).append('\n');
            }
            result.append(JavaPrimitiveSmtSemantics.INT_WRAP_DEFINITION)
                    .append('\n');
            result.append(JavaPrimitiveSmtSemantics.LONG_WRAP_DEFINITION)
                    .append('\n');
            if (usesJavaIntString) {
                result.append(VmTermLowering.JAVA_INT_TO_STRING)
                        .append('\n');
            }
            for (Map.Entry<String, Sort> declaration
                    : declarations.entrySet()) {
                result.append("(declare-const ").append(declaration.getKey())
                        .append(' ').append(declaration.getValue().smt)
                        .append(")\n");
            }
            for (SharedTermDefinition definition
                    : shared.definitions) {
                result.append("(declare-const ").append(definition.name)
                        .append(' ').append(definition.sort.smt)
                        .append(")\n");
            }
            for (String declaration : shared.functionDeclarations) {
                result.append(declaration).append('\n');
            }
            for (SymbolNames symbol : names.values()) {
                if (symbol.sort != Sort.REF) continue;
                result.append("(define-fun ")
                        .append(symbol.nullness)
                        .append(" () Bool (= ")
                        .append(symbol.solver)
                        .append(" nullRef))\n");
            }
            // NaN needs a discriminator because its IEEE payload is arbitrary.
            for (String raw : controlledSymbols) {
                Sort sort = names(raw).sort;
                if (sort == null || !sort.floating()) continue;
                SymbolNames names = names(raw);
                String name = names.solver;
                String bits = names.floatingBits;
                String isNaN = names.floatingNaN;
                result.append("(define-fun ").append(bits)
                        .append(" () (_ BitVec ")
                        .append(sort == Sort.FLOAT32 ? 32 : 64)
                        .append(") (fp.to_ieee_bv ").append(name)
                        .append("))\n");
                result.append("(define-fun ").append(isNaN)
                        .append(" () Bool (fp.isNaN ").append(name)
                        .append("))\n");
            }
            for (SharedTermDefinition definition
                    : shared.definitions) {
                result.append("(assert (= ").append(definition.name)
                        .append(' ').append(definition.body).append("))\n");
            }
            for (String assertion : shared.assertions) {
                result.append("(assert ").append(assertion).append(")\n");
            }
            for (String assertion : softAssertions) {
                result.append("(assert-soft ").append(assertion)
                        .append(" :weight 1)\n");
            }
            result.append("(check-sat)\n");
            List<String> modelNames = new ArrayList<>();
            for (String raw : controlledSymbols) {
                Sort sort = names(raw).sort;
                if (sort != null && !sort.containerState()) {
                    SymbolNames names = names(raw);
                    if (sort.floating()) {
                        modelNames.add(names.floatingBits);
                        modelNames.add(names.floatingNaN);
                    } else if (sort == Sort.STRING) {
                        modelNames.add(names.solver);
                        modelNames.add(names.nullness);
                    } else if (sort == Sort.REF) {
                        modelNames.add(names.nullness);
                    } else {
                        modelNames.add(names.solver);
                    }
                }
            }
            Collections.sort(modelNames);
            if (!modelNames.isEmpty()) {
                result.append("(get-value (");
                for (int index = 0; index < modelNames.size(); index++) {
                    if (index > 0) result.append(' ');
                    result.append(modelNames.get(index));
                }
                result.append("))\n");
            }
            return result.toString();
        }
    }

    private static final class SharedTermEmission {
        private final List<SharedTermDefinition> definitions;
        private final List<String> functionDeclarations;
        private final List<String> assertions;

        private SharedTermEmission(List<SharedTermDefinition> definitions,
                                   List<String> functionDeclarations,
                                   List<String> assertions) {
            this.definitions = definitions;
            this.functionDeclarations = functionDeclarations;
            this.assertions = assertions;
        }
    }

    private static final class SharedAliasToken {
        private final String name;
        private final int start;
        private final int end;

        private SharedAliasToken(String name, int start, int end) {
            this.name = name;
            this.start = start;
            this.end = end;
        }
    }


    private static final class SharedTermDefinition {
        private final String name;
        private final Sort sort;
        private final String body;

        private SharedTermDefinition(String name, Sort sort, String body) {
            this.name = name;
            this.sort = sort;
            this.body = body;
        }
    }


    /**
     * Prefer the concrete values from the observed execution while leaving
     * every path predicate hard.  MaxSMT therefore changes only the smallest
     * number of replay controls needed for the requested flip.
     */
    private static void preferObservedReplayControls(
            Encoder encoder, Set<String> replayControls,
            List<JsonObject> actions) {
        List<String> ordered = new ArrayList<>(replayControls);
        Collections.sort(ordered);
        for (String raw : ordered) {
            SymbolNames names = encoder.names(raw);
            if (names == null) continue;
            ActionMatch match = bestAction(raw, actions, names.sort);
            String observed = observedPrimitiveLiteral(
                    match == null ? null : match.action, names.sort);
            if (!observed.isEmpty()) {
                encoder.softAssertions.add("(= " + names.solver + " "
                        + observed + ")");
            }
        }
    }

    /** SMT literal for a runtime-recorded Java primitive, or no preference
     * when the action does not carry an exact observation. */
    private static String observedPrimitiveLiteral(JsonObject action,
                                                    Sort sort) {
        if (action == null || !optionalBool(action, "observed", false)
                || !action.has("primitiveValue")
                || action.get("primitiveValue").isJsonNull()) {
            return "";
        }
        String value = optionalString(action, "primitiveValue").trim();
        if (sort == Sort.BOOL) {
            return "true".equals(value) || "false".equals(value)
                    ? value : "";
        }
        if (sort != Sort.INT || value.isEmpty()) return "";
        try {
            BigInteger parsed = new BigInteger(value);
            return parsed.signum() < 0
                    ? "(- " + parsed.negate() + ")" : parsed.toString();
        } catch (NumberFormatException malformed) {
            return "";
        }
    }

    private static ModelProjection modelAssignments(
            Encoder encoder, Map<String, String> values,
            List<JsonObject> actions,
            List<List<ConfiguredSourcePhaseContract.Occurrence>>
                    configuredSourcePhaseCatalogs,
            Set<String> projectedSymbols) {
        JsonArray result = new JsonArray();
        Set<String> unresolved = new LinkedHashSet<>(projectedSymbols);
        for (String raw : encoder.controlledSymbols) {
            if (!projectedSymbols.contains(raw)) continue;
            SymbolNames names = encoder.names(raw);
            if (names == null || names.sort == Sort.REF
                    || names.sort == Sort.STRING
                    || names.sort.containerState()) {
                continue;
            }
            ConfiguredSourceMatch source = configuredSourceResolution(
                    raw, configuredSourcePhaseCatalogs, names.sort);
            ActionMatch symbolicAction = registeredSymbolicAction(
                    raw, actions, names.sort);
            if ((source == null) == (symbolicAction == null)) continue;
            String modelName = names.sort.floating()
                    ? names.floatingBits : names.solver;
            String value = values.get(modelName);
            String nanValue = names.sort.floating()
                    ? values.get(names.floatingNaN) : "";
            if (value == null || names.sort.floating()
                    && !("true".equals(nanValue)
                    || "false".equals(nanValue))) {
                continue;
            }
            JsonObject assignment = new JsonObject();
            assignment.addProperty("engineSymbol", raw);
            if (source != null) {
                assignment.addProperty("inputSymbol",
                        "SOURCE_PHASE:" + source.sourcePhaseId);
                assignment.addProperty("configuredSourceId",
                        source.sourceId);
                assignment.addProperty("configuredSourcePhaseId",
                        source.sourcePhaseId);
                assignment.addProperty("configuredSourceFieldSignature",
                        source.fieldSignature);
            } else {
                assignment.addProperty("inputSymbol",
                        optionalString(symbolicAction.action, "symbol"));
            }
            if (names.sort.floating()) {
                String descriptor = names.sort == Sort.FLOAT32 ? "F" : "D";
                String decoded = "true".equals(nanValue) ? "NaN"
                        : SmtModelValueCodec.floatingPointBitsToJavaLiteral(
                        value, descriptor);
                if (decoded == null) continue;
                assignment.addProperty("valueType", "REAL");
                assignment.addProperty("value", decoded);
            } else {
                assignment.addProperty("valueType", names.sort.replayName());
                assignment.addProperty("value",
                        SmtModelValueCodec.normalizeScalar(value));
            }
            result.add(assignment);
            unresolved.remove(raw);
        }
        return new ModelProjection(result, unresolved);
    }


    private static List<JsonObject> materializationActions(
            JsonObject activation) throws IOException {
        InputActionCatalog catalog;
        try {
            catalog = InputActionCatalog.decode(activation);
        } catch (IllegalArgumentException malformed) {
            throw new IOException("invalid input actions: "
                    + malformed.getMessage(), malformed);
        }
        List<JsonObject> declared = new ArrayList<>();
        for (JsonElement element : catalog.all()) {
            declared.add(element.getAsJsonObject());
        }
        declared.sort(Comparator.comparing(
                value -> optionalString(value, "symbol")));
        return declared;
    }

    private static final class PathQuery {
        private final String queryKey;
        private final BranchReplayContract replayContract;
        private final SolverPathContext pathContext;
        private final String sourceActivationOccurrenceId;

        private PathQuery(String queryKey,
                          BranchReplayContract replayContract,
                          SolverPathContext pathContext,
                          String sourceActivationOccurrenceId) {
            this.queryKey = queryKey;
            this.replayContract = replayContract;
            this.pathContext = pathContext;
            // SharedExpressionTable.expand() has already reconstructed one
            // immutable expression DAG for this worker.  This array is only
            // read during solving; a defensive deep copy would recursively
            // expand the DAG once more before Z3 is even started.
            this.sourceActivationOccurrenceId =
                    sourceActivationOccurrenceId;
        }

        private static PathQuery decode(JsonObject task) throws IOException {
            if (optionalInteger(task, "schemaVersion", -1) != 3
                    || !"REGION_PATH_FLIP".equals(optionalString(task, "kind"))) {
                throw new IOException(
                        "canonical path task requires REGION_PATH_FLIP "
                                + "schema 3");
            }
            String queryKey = optionalString(task, "queryKey");
            if (!canonicalQueryKey(queryKey)) {
                throw new IOException(
                        "canonical path task requires SHA-256 queryKey");
            }
            try {
                return new PathQuery(queryKey,
                        BranchReplayContract.fromImmutableJson(
                        requiredObject(task, "replayContract")),
                        SolverPathContext.fromJson(requiredObject(task,
                                "solverPathContext")),
                        optionalString(task, "sourceActivationOccurrenceId"));
            } catch (IllegalArgumentException malformed) {
                throw new IOException("invalid canonical path task: "
                        + malformed.getMessage(), malformed);
            }
        }
    }

    /** Exact executable scalar input action that the replay runtime can set. */
    private static ActionMatch registeredSymbolicAction(
            String raw, List<JsonObject> actions, Sort expectedSort) {
        if (expectedSort != Sort.BOOL && expectedSort != Sort.INT
                && (expectedSort == null || !expectedSort.floating())) {
            return null;
        }
        return bestAction(raw, actions, expectedSort);
    }

    private static ActionMatch bestAction(
            String raw, List<JsonObject> actions, Sort expectedSort) {
        ActionMatch best = null;
        int bestLength = -1;
        for (JsonObject action : actions) {
            if (!executable(action)
                    || expectedSort != null
                    && materializationSort(action)
                    != expectedSort) {
                continue;
            }
            String symbol = optionalString(action, "symbol");
            if (symbol.isEmpty()) continue;
            List<JsonArray> paths = new ArrayList<>();
            paths.add(new JsonArray());
            if (array(action, "fieldPath").size() > 0)
                paths.add(array(action, "fieldPath"));
            for (JsonElement path : array(action, "fieldPaths")) {
                if (path.isJsonArray()) paths.add(path.getAsJsonArray());
            }
            for (JsonArray path : paths) {
                List<String> segments = stringList(path);
                if (segments.size() != path.size()) continue;
                // The same dotted label the Runtime builds for this path, so
                // a blank segment refuses here exactly as it does there.
                String suffix = FieldPathSpec.join(segments);
                if (!segments.isEmpty() && suffix.isEmpty()) continue;
                String label = suffix.isEmpty() ? symbol
                        : symbol + "." + suffix;
                if (matchesEngineSymbol(raw, label)
                        && label.length() > bestLength) {
                    best = new ActionMatch(action);
                    bestLength = label.length();
                }
            }
        }
        return best;
    }

    /**
     * Resolves one VM source root to the exact configured Java field whose
     * mint site produced it.  Every occurrence of a declared site is its own
     * symbol, so the task's PUBLISH catalog of mint SITES is the authority;
     * the engine label already names one exact site execution.
     */
    private static ConfiguredSourceMatch configuredSourceResolution(
            String raw,
            List<List<ConfiguredSourcePhaseContract.Occurrence>> phaseCatalogs,
            Sort expectedSort) {
        if (raw == null || raw.isEmpty()
                || expectedSort == null || expectedSort == Sort.UNKNOWN
                || expectedSort == Sort.REF || expectedSort == Sort.STRING
                || expectedSort.containerState()) {
            return null;
        }
        ConfiguredSourceMatch selected = null;
        for (List<ConfiguredSourcePhaseContract.Occurrence> mintSites
                : phaseCatalogs == null
                ? Collections.<List<ConfiguredSourcePhaseContract.Occurrence>>
                emptyList() : phaseCatalogs) {
            for (ConfiguredSourcePhaseContract.Occurrence phase : mintSites) {
                FieldPathSpec.DeclaredField field =
                        FieldPathSpec.declaredField(phase.fieldSignature());
                if (field == null
                        || sortOfJava(field.type()) != expectedSort
                        || !matchesEngineSymbol(raw,
                        SymbolicSourceEvidence.engineLabelForPhase(
                                phase.phaseId(), phase.sourceId()))) {
                    continue;
                }
                ConfiguredSourceMatch match = new ConfiguredSourceMatch(
                        phase.phaseId(), phase.sourceId(), field.signature());
                // A phase id is the variable, and it repeats: once per
                // execution of its site, and once in every linked member's
                // catalog that saw that site
                // (ConfiguredSourcePhaseContract:143).  Two occurrences of
                // one variable are that variable, not an ambiguity, and
                // refusing on the second made a root the replay can set
                // read as one it cannot.  What is still ambiguous is one
                // engine symbol matching two different variables, and that
                // is what this refuses.
                if (selected != null) {
                    if (!selected.sameVariable(match)) return null;
                    continue;
                }
                selected = match;
            }
        }
        return selected;
    }

    private static ReplaySupport classifyReplaySupport(
            Encoder encoder, Set<String> symbols, List<JsonObject> actions,
            List<List<ConfiguredSourcePhaseContract.Occurrence>>
                    configuredSourcePhaseCatalogs) {
        Set<String> writable = new LinkedHashSet<>();
        Set<String> unresolved = new LinkedHashSet<>();
        for (String symbol : symbols) {
            if (VmExpressionIr.SYMBOLIC_NULL.equals(symbol)
                    || "V".equals(symbol)) continue;
            SymbolNames names = encoder.names(symbol);
            if (names != null
                    && fixedNonNullReference(symbol, names.sort)) {
                continue;
            }
            // A handoff symbol is a replay control like a configured source:
            // the runtime mints one variable per handoff occurrence and
            // answers an assignment to it by returning the model value
            // instead of the value that arrived.  It is identified by its
            // own prefix and needs no catalog, because the mint that owns
            // it is the attach the row already names.
            boolean registered = names != null
                    && (symbol.contains(
                            PathMergeComposer.HANDOFF_SYMBOL_MARK)
                    || configuredSourceResolution(symbol,
                    configuredSourcePhaseCatalogs, names.sort) != null
                    || registeredSymbolicAction(symbol, actions, names.sort)
                    != null);
            if (registered) {
                writable.add(symbol);
                encoder.controlledSymbols.add(symbol);
            } else {
                unresolved.add(symbol);
            }
        }
        return new ReplaySupport(writable, unresolved);
    }

    private static Sort materializationSort(JsonObject action) {
        String javaType = optionalString(action, "javaType");
        String normalized = javaType.replace('/', '.');
        if ("java.lang.Boolean".equals(normalized)) return Sort.BOOL;
        if ("java.lang.Byte".equals(normalized)
                || "java.lang.Short".equals(normalized)
                || "java.lang.Character".equals(normalized)
                || "java.lang.Integer".equals(normalized)
                || "java.lang.Long".equals(normalized)) {
            return Sort.INT;
        }
        if ("java.lang.Float".equals(normalized)) return Sort.FLOAT32;
        if ("java.lang.Double".equals(normalized)) return Sort.FLOAT64;
        return sortOfJava(javaType);
    }

    private static boolean matchesEngineSymbol(
            String engine, String semantic) {
        if (engine == null || semantic == null || semantic.isEmpty()) {
            return false;
        }
        if (engine.equals(semantic)) return true;
        String payload = "";
        int fieldMarker = engine.startsWith("M_")
                ? engine.indexOf("_field_", 2) : -1;
        if (fieldMarker >= 0) {
            payload = engine.substring(fieldMarker + "_field_".length());
        } else if (engine.startsWith("M_L'")) {
            int runtimeTypeEnd = engine.indexOf("'_", 4);
            if (runtimeTypeEnd > 4) {
                payload = engine.substring(runtimeTypeEnd + 2);
            }
        }
        return payload.equals(semantic)
                || payload.startsWith(semantic + ".occ.")
                || payload.startsWith(semantic + "_");
    }

    private static boolean executable(JsonObject action) {
        return "SYMBOLIC".equals(optionalString(action, "mode"));
    }

    private static final class ActionMatch {
        private final JsonObject action;

        private ActionMatch(JsonObject action) {
            this.action = action;
        }
    }

    private static final class ConfiguredSourceMatch {
        private final String sourcePhaseId;
        private final String sourceId;
        private final String fieldSignature;

        private ConfiguredSourceMatch(String sourcePhaseId, String sourceId,
                                      String fieldSignature) {
            this.sourcePhaseId = sourcePhaseId;
            this.sourceId = sourceId;
            this.fieldSignature = fieldSignature;
        }

        /** Whether two matches name one replay-controllable variable. */
        private boolean sameVariable(ConfiguredSourceMatch other) {
            return other != null
                    && sourcePhaseId.equals(other.sourcePhaseId)
                    && sourceId.equals(other.sourceId)
                    && fieldSignature.equals(other.fieldSignature);
        }
    }

    static SolverOutput run(Path executable, String input,
                            long timeoutMillis)
            throws IOException, InterruptedException {
        long startedNanos = System.nanoTime();
        long budgetNanos = TimeUnit.MILLISECONDS.toNanos(
                Math.max(0L, timeoutMillis));
        byte[] encoded = input.getBytes(StandardCharsets.UTF_8);
        if (remainingNanos(startedNanos, budgetNanos) <= 0L) {
            return new SolverOutput(true, "");
        }
        ProcessBuilder builder = new ProcessBuilder(executable.toString(),
                "-in", "-smt2");
        builder.redirectErrorStream(true);
        Process process = builder.start();
        AtomicReference<IOException> writeFailure = new AtomicReference<>();
        AtomicReference<IOException> readFailure = new AtomicReference<>();
        AtomicReference<String> stdout = new AtomicReference<>("");
        Thread writer = new Thread(() -> {
            try (OutputStream stream = process.getOutputStream()) {
                stream.write(encoded);
            } catch (IOException failure) {
                writeFailure.set(failure);
            }
        }, "graphchecker-z3-writer");
        Thread reader = new Thread(() -> {
            try {
                stdout.set(readAll(process.getInputStream()));
            } catch (IOException failure) {
                readFailure.set(failure);
            }
        }, "graphchecker-z3-reader");
        writer.setDaemon(true);
        reader.setDaemon(true);
        writer.start();
        reader.start();
        try {
            long remaining = remainingNanos(startedNanos, budgetNanos);
            if (remaining <= 0L
                    || !process.waitFor(remaining, TimeUnit.NANOSECONDS)) {
                terminate(process, writer, reader);
                return new SolverOutput(true, "");
            }
            if (!joinWithin(writer, startedNanos, budgetNanos)
                    || !joinWithin(reader, startedNanos, budgetNanos)) {
                terminate(process, writer, reader);
                return new SolverOutput(true, "");
            }
            if (writeFailure.get() != null) throw writeFailure.get();
            if (readFailure.get() != null) throw readFailure.get();
            return new SolverOutput(false, stdout.get());
        } catch (InterruptedException interrupted) {
            process.destroyForcibly();
            writer.interrupt();
            reader.interrupt();
            throw interrupted;
        }
    }

    private static long remainingNanos(long startedNanos,
                                       long budgetNanos) {
        return budgetNanos - (System.nanoTime() - startedNanos);
    }

    private static boolean joinWithin(Thread thread, long startedNanos,
                                      long budgetNanos)
            throws InterruptedException {
        long remaining = remainingNanos(startedNanos, budgetNanos);
        if (remaining <= 0L) return !thread.isAlive();
        long millis = Math.max(1L,
                TimeUnit.NANOSECONDS.toMillis(remaining));
        thread.join(millis);
        return !thread.isAlive();
    }

    private static void terminate(Process process, Thread writer,
                                  Thread reader) {
        process.destroyForcibly();
        writer.interrupt();
        reader.interrupt();
    }

    private static String readAll(InputStream stream) throws IOException {
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[4096];
        int read;
        while ((read = stream.read(buffer)) >= 0) {
            output.write(buffer, 0, read);
        }
        return new String(output.toByteArray(), StandardCharsets.UTF_8);
    }

    static final class SolverOutput {
        final boolean timedOut;
        final String stdout;

        private SolverOutput(boolean timedOut, String stdout) {
            this.timedOut = timedOut;
            this.stdout = stdout;
        }

        String status() {
            if (timedOut) return "timeout";
            return firstLine(stdout);
        }

        String diagnostic() {
            return timedOut ? "solver timeout" : stdout;
        }

    }

    static Map<String, String> parseGetValues(String output) {
        Map<String, String> result = new LinkedHashMap<>();
        int newline = output.indexOf('\n');
        if (newline < 0) return result;
        List<String> rows = SmtModelValueCodec.applicationItems(
                output.substring(newline + 1).trim());
        if (rows == null) return result;
        for (String row : rows) {
            List<String> pair = SmtModelValueCodec.applicationItems(row);
            if (pair != null && pair.size() == 2) {
                result.put(pair.get(0), pair.get(1));
            }
        }
        return result;
    }

    /** The composer's {@code SplitPrefix}, for this caller. */
    private static final class SplitPrefix {
        private final JsonElement integerExpression;
        private final String gap;

        private SplitPrefix(JsonElement integerExpression, String gap) {
            this.integerExpression = integerExpression;
            this.gap = firstNonBlank(gap);
        }

        private static SplitPrefix complete(JsonElement integerExpression) {
            return new SplitPrefix(integerExpression, "");
        }

        private static SplitPrefix gap(String gap) {
            return new SplitPrefix(null, gap);
        }

        private boolean complete() {
            return integerExpression != null && gap.isEmpty();
        }
    }

    private static JsonObject baseRecord(String queryKey) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "REGION_PATH_EXPLORATION_RECORD");
        result.addProperty("queryKey", queryKey);
        return result;
    }

    static boolean canonicalQueryKey(String value) {
        return value != null && value.matches("[0-9a-f]{64}");
    }

    private static boolean regionInput(String raw) {
        return raw != null && raw.matches(
                ".*REGION(?:[._-][A-Za-z0-9-]+)+[._-]in[._-]"
                        + "[A-Za-z0-9-]+.*");
    }

    /** VM placeholders and allocation witnesses already denote concrete oops. */
    private static boolean fixedNonNullReference(String raw, Sort sort) {
        return sort == Sort.REF && raw != null
                && (raw.startsWith("P_L")
                || VmExpressionIr.isExecutionLocalStructuralWitness(raw));
    }

    /** This encoder's own answer to "is this Java type a String?". */
    private static final Predicate<String> STRING_TYPED =
            type -> sortOfJava(type) == Sort.STRING;

    private static Sort sortOfJava(String javaType) {
        String descriptor = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                javaType);
        if ("Z".equals(descriptor)) return Sort.BOOL;
        if (descriptor.length() == 1 && "BCSIJ".contains(descriptor)) {
            return Sort.INT;
        }
        FloatingKind floating = JavaPrimitiveSmtSemantics
                .floatingKindOfJavaType(javaType);
        if (floating == FloatingKind.JAVA_FLOAT) return Sort.FLOAT32;
        if (floating == FloatingKind.JAVA_DOUBLE) return Sort.FLOAT64;
        if ("Ljava/lang/String;".equals(descriptor)) return Sort.STRING;
        return descriptor.startsWith("L") || descriptor.startsWith("[")
                ? Sort.REF : Sort.UNKNOWN;
    }

    private static String safeName(String value) {
        String safe = value.replaceAll("[^A-Za-z0-9_]", "_");
        if (safe.isEmpty()) safe = "empty";
        if (Character.isDigit(safe.charAt(0))) safe = "n_" + safe;
        return safe.length() > 80 ? safe.substring(0, 80) : safe;
    }

    private static final class SymbolNames {
        private final Sort sort;
        private final IntegralWidth width;
        private final String solver;
        private final String nullness;
        private final String floatingBits;
        private final String floatingNaN;

        private SymbolNames(String raw, Sort sort, IntegralWidth width,
                            SmtSymbolTable symbols) {
            this.sort = sort;
            this.width = width;
            String safe = safeName(raw);
            String digest = sha256(raw);
            solver = symbols.mintFromDigest("sym__" + safe + "__",
                    digest, raw, 10);
            String nullableKind = sort == Sort.STRING ? "string"
                    : sort == Sort.REF ? "reference" : "";
            String nullIdentity = nullableKind + "-null\u0000" + raw;
            nullness = nullableKind.isEmpty() ? ""
                    : symbols.mint("sym__" + nullableKind + "_is_null__"
                    + safe + "__", nullIdentity, 10);
            floatingBits = symbols.mintFromDigest("sym__fpbits__" + safe
                    + "__", digest, raw, 10);
            floatingNaN = symbols.mintFromDigest("sym__fpisnan__" + safe
                    + "__", digest, raw, 10);
        }
    }

    private static String firstLine(String value) {
        if (value == null) return "";
        int newline = value.indexOf('\n');
        return (newline < 0 ? value : value.substring(0, newline)).trim();
    }

    private static List<String> stringList(JsonArray values) {
        List<String> result = new ArrayList<>();
        for (JsonElement value : values) {
            if (value.isJsonPrimitive()
                    && value.getAsJsonPrimitive().isString()
                    && !value.getAsString().isEmpty()) {
                result.add(value.getAsString());
            }
        }
        return result;
    }

    private static JsonArray strings(Iterable<String> values) {
        JsonArray result = new JsonArray();
        for (String value : values) result.add(value);
        return result;
    }

}
