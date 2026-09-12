package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.IntegralWidth;
import edu.uva.liftlab.graphchecker.concolic.VmTermLowering.GuardedReadUse;
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
        JsonArray branchConstraints = replayContract
                .requiredPathPredicates();
        JsonArray contextConstraints = query.pathContext.expressions();
        List<JsonObject> actions = materializationActions(activation);
        List<JsonObject> targetActions = materializationActions(
                primaryActivation);
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
            encoder.captureTargetContainerReads = target;
            Set<String> symbols;
            try {
                symbols = encoder.addConstraint(branchConstraints.get(index),
                        "q_branch_" + index);
            } finally {
                encoder.captureTargetContainerReads = false;
            }
            replayFrontier.addAll(symbols);
            if (target) {
                targetSymbols.addAll(symbols);
            }
        }
        replayFrontier.addAll(encoder.bindConsumerFamilyDependencies(
                query.consumerAnchorCaseDependencies,
                query.sourceActivationOccurrenceId));
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
        encoder.finishGuardedReadSelections();
        encoder.bindTargetContainerReads(targetActions);
        String smt = encoder.finish();
        JsonObject record = baseRecord(query.queryKey);
        record.add("unsupported", strings(encoder.unsupported));
        if (!encoder.unsupported.isEmpty()) {
            record.addProperty("status", "UNSUPPORTED");
            record.addProperty("reason", "UNSUPPORTED_EXPRESSION_IR");
            return new Result(record, smt, new JsonArray(),
                    replayContract);
        }

        if (!encoder.targetContainerGaps.isEmpty()) {
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason",
                    "TARGET_CONTAINER_READ_IS_NOT_MATERIALIZABLE");
            record.add("unresolvedTargetContainerReads",
                    strings(encoder.targetContainerGaps));
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
        ModelProjection containerProjection = targetContainerAssignments(
                encoder, values, replayContract.source().occurrence());
        for (JsonElement assignment : containerProjection.assignments) {
            projection.assignments.add(assignment);
        }
        projection.unresolved.addAll(containerProjection.unresolved);
        JsonArray assignments = projection.assignments;
        if (projectedSymbols.isEmpty()
                && encoder.targetContainerModels.isEmpty()) {
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

    private static final class Encoder implements VmTermLowering.Policy {
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
        private final Set<String> additionalModelNames =
                new LinkedHashSet<>();
        private final Set<String> javaIntRangeAssertions =
                new LinkedHashSet<>();
        private final Set<String> usedConsumerFamilies =
                new LinkedHashSet<>();
        private final Set<String> boundConsumerFamilies =
                new LinkedHashSet<>();
        private final Set<String> activeConsumerMerges =
                new LinkedHashSet<>();
        /** A family chooses a case only where its propagated value is used. */
        private final Map<String, Set<String>> consumerFamilyActivations =
                new LinkedHashMap<>();
        private final Map<String, Set<String>> consumerFamilySelectors =
                new LinkedHashMap<>();
        /** RF selector -> exact producer case, grouped by PC dependency. */
        private final Map<String, Map<String, GuardedReadCaseBinding>>
                readFromWriterCases = new LinkedHashMap<>();
        /** Writer-case partition admitted for each RF dependency family. */
        private final Map<String, Set<String>> readFromCaseSelectors =
                new LinkedHashMap<>();
        /** Replay observations which refine one stable local case. */
        private final Map<String, Set<String>> caseObservationSelectors =
                new LinkedHashMap<>();
        /** One observation selector must never refine two base cases. */
        private final Map<String, String> observationBaseCases =
                new LinkedHashMap<>();
        /** RF bindings are discovered while nested case PCs are lowered. */
        private final Set<String> boundReadFromWriterBindings =
                new LinkedHashSet<>();
        private final Map<String, Set<String>> guardedReadSelectors =
                new LinkedHashMap<>();
        private final Map<String, Map<String, GuardedReadUse>> guardedReadUses =
                new LinkedHashMap<>();
        private final Map<String, Map<String, Set<String>>>
                guardedSelectorActivationGuards = new LinkedHashMap<>();
        /** Exact target reads whose propagated value can be replayed at the
         * same live container access. */
        private final Map<String, TargetContainerRead> targetContainerReads =
                new LinkedHashMap<>();
        private final List<TargetContainerRead> targetContainerModels =
                new ArrayList<>();
        private final Set<String> targetContainerGaps =
                new LinkedHashSet<>();
        private final SharedExpressionTable.Anchors targetReadAnchors =
                new SharedExpressionTable.Anchors();
        private String currentReadActivationGuard = "true";
        private boolean captureTargetContainerReads;
        private int guardedReadDepth;
        private boolean usesJavaIntString;
        private Set<String> currentConstraintSymbols;


        // The shared lowering's policies: how a sub-expression is lowered,
        // what an unsupported construct becomes, how Java evaluation
        // definedness is carried, and how a rendering is proved.

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
            return ConcolicConstraintSolver.castSort(descriptor);
        }

        @Override
        public VmTermLowering.RenderedInteger renderedInteger(
                JsonElement element, String origin) {
            SplitPrefix match = exactSplitPrefix(element);
            if (!match.complete()) {
                return VmTermLowering.RenderedInteger.gap(
                        "ROUNDTRIP_NOT_PROVED_" + match.gap);
            }
            return VmTermLowering.RenderedInteger.of(term(
                    match.integerExpression, Sort.INT, origin + ":parseInt"));
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
            if (expression == null || expression.isJsonNull()
                    || !expression.isJsonObject()) {
                unsupported.add(origin + ":MISSING_OR_NON_OBJECT_EXPRESSION");
                return null;
            }
            JsonObject object = expression.getAsJsonObject();
            String type = optionalString(object, "_type");
            if ("SymbolExpression".equals(type)) {
                return symbol(object, origin);
            }
            if (ContainerSmtCodec.constantKind(type)) {
                return constant(object, expected, origin);
            }
            if ("PlaceholderExpression".equals(type)) {
                return placeholder(object, origin);
            }
            if ("BinaryExpression".equals(type)) {
                return binary(object, origin);
            }
            if ("OpStrExpression".equals(type)) {
                return stringOperation(object, origin);
            }
            if ("NotExpression".equals(type)) {
                Term operand = term(object.get("_operand"), Sort.BOOL,
                        origin + ":not");
                if (operand == null || operand.sort != Sort.BOOL) {
                    unsupported.add(origin + ":MALFORMED_NOT");
                    return null;
                }
                return Term.vm("(not " + operand.text + ")", Sort.BOOL);
            }
            if ("TypeCastExpression".equals(type)) {
                return typeCast(object, origin);
            }
            if ("MethodExpression".equals(type)) {
                return methodTerm(object, origin);
            }
            if (SharedStateEvidence.GUARDED_READ_TYPE.equals(type)) {
                return guardedReadTerm(object, expected, origin);
            }
            if (SymbolicPropagationClosure.ITE_TYPE.equals(type)) {
                return consumerCaseMergeTerm(object, expected, origin);
            }
            if (VmExpressionIr.CONSUMER_BOUNDARY_TYPE.equals(type)
                    || VmExpressionIr.CONSUMER_BOUNDARY_REFERENCE_TYPE
                    .equals(type)) {
                return term(object.get(VmExpressionIr.EXPRESSION), expected,
                        origin + ":consumer-boundary");
            }
            if (ContainerSmtCodec.handles(object)) {
                return containerTerm(object, origin);
            }
            if (ContainerSmtCodec.handlesField(object)) {
                return containerFieldTerm(object, origin);
            }
            unsupported.add(origin + ":TYPE:" + firstNonBlank(type,
                    "MISSING"));
            return null;
        }

        /** Lowers one receiver-owned value family without enumerating a
         * product with the primary region's local paths. */
        private Term consumerCaseMergeTerm(JsonObject merge, Sort expected,
                                           String origin) {
            String mergeId = optionalString(merge, "mergeId");
            String family = optionalString(merge, VmExpressionIr.FAMILY_KEY);
            JsonArray encoded = array(merge, "arms");
            if (mergeId.isEmpty() || family.isEmpty()
                    || encoded.size() == 0
                    || !activeConsumerMerges.add(mergeId)) {
                unsupported.add(origin + ":MALFORMED_OR_CYCLIC_"
                        + SymbolicPropagationClosure.ITE_TYPE + ":"
                        + firstNonBlank(mergeId, family));
                return null;
            }
            usedConsumerFamilies.add(family);
            consumerFamilyActivations.computeIfAbsent(family,
                    ignored -> new LinkedHashSet<>()).add(firstNonBlank(
                    currentReadActivationGuard, "true"));
            try {
                List<String> selectors = new ArrayList<>();
                List<Term> values = new ArrayList<>();
                Sort sort = expected;
                List<JsonElement> orderedArms = new ArrayList<>();
                for (JsonElement element : encoded) {
                    orderedArms.add(element);
                }
                // Case selectors are stable content-addressed identities and
                // already define the canonical arm order.  Re-rendering each
                // arm recursively here expands the propagated DAG into a tree.
                orderedArms.sort(Comparator.comparing(element ->
                        element.isJsonObject()
                                ? optionalString(element.getAsJsonObject(), "selector")
                                : ""));
                for (JsonElement element : orderedArms) {
                    if (!element.isJsonObject()) {
                        unsupported.add(origin
                                + ":CONSUMER_MERGE_ARM_NOT_OBJECT");
                        return null;
                    }
                    JsonObject arm = element.getAsJsonObject();
                    String selector = optionalString(arm, "selector");
                    JsonElement expression = arm.get("expression");
                    if (selector.isEmpty() || expression == null) {
                        unsupported.add(origin
                                + ":CONSUMER_MERGE_ARM_INCOMPLETE");
                        return null;
                    }
                    declarations.put(selector, Sort.BOOL);
                    additionalModelNames.add(selector);
                    String previousGuard = currentReadActivationGuard;
                    currentReadActivationGuard = andGuard(previousGuard,
                            selector);
                    Term value;
                    try {
                        value = term(expression, sort,
                                origin + ":consumer-arm:" + selector);
                    } finally {
                        currentReadActivationGuard = previousGuard;
                    }
                    if (value == null) return null;
                    if (sort == null) sort = value.sort;
                    if (value.sort != sort) {
                        unsupported.add(origin
                                + ":CONSUMER_MERGE_ARM_SORT_CONFLICT");
                        return null;
                    }
                    selectors.add(selector);
                    values.add(value);
                }
                String value = values.get(values.size() - 1).text;
                IntegralWidth width = values.get(0).integralWidth;
                String nullness = sort == Sort.STRING
                        ? values.get(values.size() - 1).stringNullness : "";
                for (Term arm : values) {
                    if (arm.integralWidth != width) {
                        width = IntegralWidth.NONE;
                    }
                    if (sort == Sort.STRING
                            && arm.stringNullness.isEmpty()) {
                        unsupported.add(origin
                                + ":CONSUMER_MERGE_STRING_NULLNESS_MISSING");
                        return null;
                    }
                }
                for (int index = values.size() - 2; index >= 0; index--) {
                    Term arm = values.get(index);
                    boolean sameValue = arm.text.equals(value);
                    boolean sameNullness = sort != Sort.STRING
                            || arm.stringNullness.equals(nullness);
                    if (sameValue && sameNullness) continue;
                    value = "(ite " + selectors.get(index) + " "
                            + arm.text + " " + value + ")";
                    if (sort == Sort.STRING) {
                        nullness = "(ite " + selectors.get(index) + " "
                                + arm.stringNullness + " " + nullness
                                + ")";
                    }
                }
                Term merged = Term.vm(value, sort, width, nullness, "");
                return shareConsumerMergeTerm(merged);
            } finally {
                activeConsumerMerges.remove(mergeId);
            }
        }

        /**
         * Shares the value term of equivalent propagated families while the
         * family keys themselves remain independent dependency authorities.
         * Every occurrence is still lowered above, so nested families and
         * read activation guards are discovered for each audited family.
         */
        private Term shareConsumerMergeTerm(Term value) {
            String sharedValue = shareSemanticTerm(value.text, value.sort);
            String nullness = value.stringNullness;
            if (value.sort == Sort.STRING && !nullness.isEmpty()) {
                nullness = shareSemanticTerm(nullness, Sort.BOOL);
            }
            return Term.vm(sharedValue, value.sort, value.integralWidth,
                    nullness, value.stringReferenceOrigin);
        }

        private String shareSemanticTerm(String text, Sort sort) {
            if (text == null || text.isEmpty() || text.charAt(0) != '(') {
                return text;
            }
            String identity = "CONSUMER_MERGE_TERM_V1\u0000"
                    + sort.replayName() + "\u0000" + text;
            String digest = sha256(identity);
            SharedTermDefinition definition = sharedTerms.get(digest);
            if (definition == null) {
                definition = new SharedTermDefinition(
                        smtSymbols.mintFromDigest(SHARED_TERM_PREFIX,
                                digest, identity, 24),
                        sort, text);
                sharedTerms.put(digest, definition);
            }
            return definition.name;
        }

        /** Defines only families reached from this flip's local expression.
         * A partial family is an admissible under-approximation; its digest
         * makes an UNSAT answer expire when another arm is observed. */
        private Set<String> bindConsumerFamilyDependencies(
                JsonArray encodedDependencies,
                String sourceActivationOccurrenceId) {
            Map<String, JsonObject> dependencies = new LinkedHashMap<>();
            for (JsonElement element : encodedDependencies) {
                if (!element.isJsonObject()) continue;
                JsonObject dependency = element.getAsJsonObject();
                String family = optionalString(dependency, VmExpressionIr.FAMILY_KEY);
                if (!family.isEmpty()) dependencies.put(family, dependency);
            }
            Set<String> symbols = new LinkedHashSet<>();
            while (true) {
                List<String> pending = new ArrayList<>();
                for (String family : usedConsumerFamilies) {
                    if (!boundConsumerFamilies.contains(family)) {
                        pending.add(family);
                    }
                }
                Collections.sort(pending);
                for (String family : pending) {
                    JsonObject dependency = dependencies.get(family);
                    if (dependency == null) {
                        unsupported.add("CONSUMER_FAMILY_DEPENDENCY_MISSING:"
                                + family);
                        boundConsumerFamilies.add(family);
                        continue;
                    }
                    bindConsumerFamilyDependency(dependency, symbols,
                            sourceActivationOccurrenceId);
                    boundConsumerFamilies.add(family);
                }
                // Lowering a dependency PC or writer path guard can expose a
                // second read from a family whose case partition was already
                // emitted.  Drain those per-read implications independently
                // of the family work set so a nested multi-hop PC cannot leave
                // its RF selector unconstrained.
                List<String> readFamilies = new ArrayList<>(
                        readFromCaseSelectors.keySet());
                Collections.sort(readFamilies);
                for (String family : readFamilies) {
                    bindReadFromWriterCases(family,
                            readFromCaseSelectors.get(family), symbols);
                }
                if (boundConsumerFamilies.containsAll(usedConsumerFamilies)
                        && !hasUnboundReadFromWriterBindings()) {
                    break;
                }
            }
            for (String family : readFromCaseSelectors.keySet()) {
                Map<String, GuardedReadCaseBinding> bindings =
                        readFromWriterCases.get(family);
                if (bindings == null || bindings.isEmpty()) {
                    unsupported.add("READ_FROM_WRITER_CASE_BINDING_MISSING:"
                            + family);
                }
            }
            for (String family : readFromWriterCases.keySet()) {
                if (boundConsumerFamilies.contains(family)
                        && !readFromCaseSelectors.containsKey(family)) {
                    unsupported.add("READ_FROM_WRITER_CASE_DEPENDENCY_MISSING:"
                            + family);
                }
            }
            finishConsumerFamilySelections();
            bindCaseObservationPartitions();
            return symbols;
        }

        private boolean hasUnboundReadFromWriterBindings() {
            for (Map.Entry<String, Set<String>> dependency
                    : readFromCaseSelectors.entrySet()) {
                for (GuardedReadCaseBinding binding
                        : readFromWriterCases.getOrDefault(
                        dependency.getKey(), Collections.emptyMap()).values()) {
                    if (!boundReadFromWriterBindings.contains(
                            readBindingIdentity(dependency.getKey(), binding))) {
                        return true;
                    }
                }
            }
            return false;
        }

        private void bindConsumerFamilyDependency(JsonObject dependency,
                                                  Set<String> symbols,
                                                  String sourceActivationOccurrenceId) {
            String family = optionalString(dependency, VmExpressionIr.FAMILY_KEY);
            JsonArray arms = array(dependency, "arms");
            List<String> selectors = new ArrayList<>();
            Set<String> baseCaseSelectors = new LinkedHashSet<>();
            for (JsonElement element : arms) {
                if (!element.isJsonObject()) continue;
                JsonObject arm = element.getAsJsonObject();
                String selector = optionalString(arm, "selector");
                String caseSelector = firstNonBlank(
                        optionalString(arm, "caseSelector"), selector);
                if (selector.isEmpty()) {
                    unsupported.add("CONSUMER_FAMILY_ARM_UNNAMED:" + family);
                    continue;
                }
                declarations.put(selector, Sort.BOOL);
                additionalModelNames.add(selector);
                selectors.add(selector);
                declarations.put(caseSelector, Sort.BOOL);
                additionalModelNames.add(caseSelector);
                baseCaseSelectors.add(caseSelector);

                String observationSelector = optionalString(arm,
                        SymbolicPropagationClosure.OBSERVATION_SELECTOR);
                if (!observationSelector.isEmpty()) {
                    if (!selector.equals(observationSelector)) {
                        unsupported.add("CONSUMER_FAMILY_OBSERVATION_SELECTOR_"
                                + "MISMATCH:" + family);
                    }
                    noteCaseObservation(caseSelector, observationSelector,
                            family);
                }

                bindConsumerPathCondition(family, selector,
                        array(arm, "pathCondition"), symbols,
                        sourceActivationOccurrenceId,
                        optionalString(arm, "occurrenceId"), -1);
            }
            if (selectors.isEmpty()) {
                unsupported.add("CONSUMER_FAMILY_HAS_NO_ARMS:" + family);
                return;
            }
            Set<String> stableSelectors = new LinkedHashSet<>(selectors);
            if (stableSelectors.size() != selectors.size()) {
                unsupported.add("CONSUMER_FAMILY_DUPLICATE_SELECTOR:"
                        + family);
            }
            Set<String> priorSelectors = consumerFamilySelectors.putIfAbsent(
                    family, stableSelectors);
            if (priorSelectors != null
                    && !priorSelectors.equals(stableSelectors)) {
                unsupported.add("CONSUMER_FAMILY_SELECTOR_SET_AMBIGUOUS:"
                        + family);
            }
            for (int left = 0; left < selectors.size(); left++) {
                for (int right = left + 1; right < selectors.size(); right++) {
                    assertions.add("(not (and " + selectors.get(left) + " "
                            + selectors.get(right) + "))");
                }
            }
            if (SymbolicPropagationClosure.READ_FROM_DEPENDENCY_POLICY.equals(
                    optionalString(dependency, "selectionPolicy"))) {
                readFromCaseSelectors.put(family,
                        new LinkedHashSet<>(baseCaseSelectors));
            }
        }

        /** Enables each case family only while one of its values is used. */
        private void finishConsumerFamilySelections() {
            List<String> families = new ArrayList<>(
                    consumerFamilySelectors.keySet());
            Collections.sort(families);
            for (String family : families) {
                Set<String> activations = consumerFamilyActivations.get(
                        family);
                Set<String> selectors = consumerFamilySelectors.get(family);
                if (activations == null || activations.isEmpty()
                        || selectors == null || selectors.isEmpty()) {
                    unsupported.add("CONSUMER_FAMILY_ACTIVATION_MISSING:"
                            + family);
                    continue;
                }
                List<String> orderedActivations = new ArrayList<>(activations);
                List<String> orderedSelectors = new ArrayList<>(selectors);
                Collections.sort(orderedActivations);
                Collections.sort(orderedSelectors);
                assertions.add("(=> " + orTerms(orderedActivations) + " "
                        + orTerms(orderedSelectors) + ")");
            }
        }

        /** Lowers one exact PC under the selector which owns its payload. */
        private void bindConsumerPathCondition(
                String family, String selector, JsonArray path,
                Set<String> symbols, String sourceActivationOccurrenceId,
                String occurrenceId, int observationIndex) {
            // This query replaces the selected activation's observed path
            // with replayContract(prefix + flipped predicate). Keep its value
            // arm, but do not pin the old whole-case PC.
            if (!sourceActivationOccurrenceId.isEmpty()
                    && sourceActivationOccurrenceId.equals(occurrenceId)) {
                return;
            }
            List<String> conditions = new ArrayList<>();
            for (int index = 0; index < path.size(); index++) {
                Set<String> previousFrontier = currentConstraintSymbols;
                currentConstraintSymbols = new LinkedHashSet<>();
                Term condition;
                String previousReadGuard = currentReadActivationGuard;
                currentReadActivationGuard = andGuard(previousReadGuard,
                        selector);
                try {
                    condition = term(path.get(index), Sort.BOOL,
                            "consumer_family_" + family + "_"
                                    + (observationIndex < 0 ? "arm"
                                    : "observation_" + observationIndex)
                                    + "_" + index);
                    symbols.addAll(currentConstraintSymbols);
                } finally {
                    currentReadActivationGuard = previousReadGuard;
                    currentConstraintSymbols = previousFrontier;
                }
                if (condition == null || condition.sort != Sort.BOOL) {
                    unsupported.add("CONSUMER_FAMILY_PC_MALFORMED:"
                            + family);
                    continue;
                }
                conditions.add(condition.text);
            }
            assertions.add("(=> " + selector + " "
                    + andTerms(conditions) + ")");
        }

        private void noteCaseObservation(String caseSelector,
                                         String observationSelector,
                                         String family) {
            if (caseSelector.isEmpty() || observationSelector.isEmpty()
                    || caseSelector.equals(observationSelector)) {
                return;
            }
            String prior = observationBaseCases.putIfAbsent(
                    observationSelector, caseSelector);
            if (prior != null && !prior.equals(caseSelector)) {
                unsupported.add("CONSUMER_OBSERVATION_BASE_CASE_AMBIGUOUS:"
                        + family + ":" + observationSelector);
                return;
            }
            caseObservationSelectors.computeIfAbsent(caseSelector,
                    ignored -> new LinkedHashSet<>()).add(
                    observationSelector);
        }

        /** A selected base case chooses exactly one of its replay variants. */
        private void bindCaseObservationPartitions() {
            List<String> cases = new ArrayList<>(
                    caseObservationSelectors.keySet());
            Collections.sort(cases);
            for (String caseSelector : cases) {
                List<String> observations = new ArrayList<>(
                        caseObservationSelectors.get(caseSelector));
                Collections.sort(observations);
                if (observations.isEmpty()) continue;
                declarations.put(caseSelector, Sort.BOOL);
                StringBuilder count = new StringBuilder("(+");
                for (String observation : observations) {
                    declarations.put(observation, Sort.BOOL);
                    count.append(" (ite ").append(observation)
                            .append(" 1 0)");
                }
                count.append(')');
                assertions.add("(= " + count + " (ite " + caseSelector
                        + " 1 0))");
            }
        }

        /** Couples a VM read-from choice to the case that created its value. */
        private void bindReadFromWriterCases(String family,
                                             Set<String> caseSelectors,
                                             Set<String> symbols) {
            Map<String, GuardedReadCaseBinding> bindings =
                    readFromWriterCases.get(family);
            if (bindings == null || bindings.isEmpty()) return;
            for (GuardedReadCaseBinding binding : bindings.values()) {
                String identity = readBindingIdentity(family, binding);
                if (!boundReadFromWriterBindings.add(identity)) continue;
                if (!caseSelectors.contains(binding.caseSelector)) {
                    unsupported.add("READ_FROM_WRITER_CASE_NOT_IN_PARTITION:"
                            + family + ":" + binding.owner);
                    continue;
                }
                assertions.add("(=> " + binding.readSelector + " "
                        + binding.caseSelector + ")");
                if (binding.pathGuard == null) {
                    unsupported.add("READ_FROM_WRITER_GUARD_MISSING:"
                            + family + ":" + binding.owner);
                    continue;
                }
                if (SharedStateEvidence.unguarded(binding.pathGuard)) {
                    continue;
                }
                Set<String> previousFrontier = currentConstraintSymbols;
                currentConstraintSymbols = new LinkedHashSet<>();
                Term guard;
                String previousReadGuard = currentReadActivationGuard;
                currentReadActivationGuard = andGuard(previousReadGuard,
                        binding.readSelector);
                try {
                    guard = term(binding.pathGuard, Sort.BOOL,
                            "read_from_writer_guard:" + family);
                    symbols.addAll(currentConstraintSymbols);
                } finally {
                    currentReadActivationGuard = previousReadGuard;
                    currentConstraintSymbols = previousFrontier;
                }
                if (guard == null || guard.sort != Sort.BOOL) {
                    unsupported.add("READ_FROM_WRITER_GUARD_MALFORMED:"
                            + family + ":" + binding.owner);
                    continue;
                }
                assertions.add("(=> " + binding.readSelector + " "
                        + guard.text + ")");
            }
        }

        private static String readBindingIdentity(
                String family, GuardedReadCaseBinding binding) {
            return family + "\n" + binding.identity();
        }

        private static String andTerms(List<String> terms) {
            if (terms.isEmpty()) return "true";
            if (terms.size() == 1) return terms.get(0);
            return "(and " + String.join(" ", terms) + ")";
        }

        private static String orTerms(List<String> terms) {
            if (terms.size() == 1) return terms.get(0);
            return "(or " + String.join(" ", terms) + ")";
        }

        /** Lowers the VM's read-time candidate snapshot directly. */
        private Term guardedReadTerm(JsonObject read, Sort expected,
                                     String origin) {
            boolean targetMapRead = captureTargetContainerReads
                    && guardedReadDepth == 0
                    && SharedStateEvidence.LOCATION_KIND_MAP_STATE.equals(
                    optionalString(object(read, "location"), "locationKind"));
            guardedReadDepth++;
            try {
                Term value = lowerGuardedReadTerm(read, expected, origin);
                if (targetMapRead && value != null) {
                    captureTargetGuardedRead(read, value, origin);
                }
                return value;
            } finally {
                guardedReadDepth--;
            }
        }

        private Term lowerGuardedReadTerm(JsonObject read, Sort expected,
                                          String origin) {
            JsonObject selectedViewState = ContainerSmtCodec
                    .selectedReadViewState(read);
            if (selectedViewState != null) {
                read = selectedViewState;
                expected = Sort.MAP;
            }
            String fault = SharedStateEvidence.guardedReadFault(read);
            String readIdentity = optionalString(read,
                    SymbolicPropagationClosure.READ_CHOICE_IDENTITY);
            JsonArray candidates = array(read, "candidates");
            Sort declared = sortOfJava(optionalString(read, "_java_type"));
            Sort sort = expected != null && expected.containerState()
                    ? expected : declared;
            if (!fault.isEmpty() || readIdentity.isEmpty()
                    || candidates.size() == 0 || sort == Sort.UNKNOWN
                    || expected != null && expected != sort) {
                unsupported.add(origin + ":UNADMITTED_GUARDED_READ:"
                        + firstNonBlank(fault, readIdentity.isEmpty()
                        ? "STABLE_READ_IDENTITY_MISSING" : "MALFORMED"));
                return null;
            }

            String activation = firstNonBlank(
                    currentReadActivationGuard, "true");
            Set<String> selectorsForRead = guardedReadSelectors
                    .computeIfAbsent(readIdentity,
                            ignored -> new LinkedHashSet<>());
            Map<String, Set<String>> selectorGuards =
                    guardedSelectorActivationGuards.computeIfAbsent(
                            readIdentity, ignored -> new LinkedHashMap<>());
            List<String> selectors = new ArrayList<>();
            List<Term> arms = new ArrayList<>();
            for (JsonElement element : candidates) {
                if (!element.isJsonObject()) {
                    unsupported.add(origin
                            + ":GUARDED_READ_CANDIDATE_NOT_OBJECT");
                    return null;
                }
                JsonObject candidate = element.getAsJsonObject();
                String candidateIdentity = optionalString(candidate,
                        SymbolicPropagationClosure.READ_CANDIDATE_IDENTITY);
                String selector = optionalString(candidate, "selector");
                String expectedSelector = GuardedReadNaming.selector(
                        readIdentity, candidateIdentity);
                if (candidateIdentity.isEmpty()
                        || !selector.equals(expectedSelector)) {
                    unsupported.add(origin
                            + ":GUARDED_READ_CANDIDATE_IDENTITY:" + selector);
                    return null;
                }
                declarations.put(selector, Sort.BOOL);
                additionalModelNames.add(selector);
                selectors.add(selector);
                selectorsForRead.add(selector);
                selectorGuards.computeIfAbsent(selector,
                        ignored -> new LinkedHashSet<>()).add(activation);
                noteReadFromWriterCase(candidate, selector, origin);

                Set<String> frontier = currentConstraintSymbols;
                currentConstraintSymbols = new LinkedHashSet<>();
                Term value;
                String previousReadGuard = currentReadActivationGuard;
                currentReadActivationGuard = andGuard(previousReadGuard,
                        selector);
                try {
                    value = term(candidate.get("expression"), sort,
                            origin + ":arm:" + candidateIdentity);
                } finally {
                    frontier.addAll(currentConstraintSymbols);
                    currentReadActivationGuard = previousReadGuard;
                    currentConstraintSymbols = frontier;
                }
                if (value == null || value.sort != sort) {
                    unsupported.add(origin
                            + ":GUARDED_READ_ARM_SORT:" + candidateIdentity);
                    return null;
                }
                arms.add(value);
            }

            String value = arms.get(arms.size() - 1).text;
            String nullness = sort == Sort.STRING
                    ? arms.get(arms.size() - 1).stringNullness : "";
            if (sort == Sort.STRING) {
                for (Term arm : arms) {
                    if (arm.stringNullness.isEmpty()) {
                        unsupported.add(origin
                                + ":GUARDED_READ_STRING_NULLNESS_MISSING");
                        return null;
                    }
                }
            }
            for (int index = arms.size() - 2; index >= 0; index--) {
                Term arm = arms.get(index);
                boolean sameValue = arm.text.equals(value);
                boolean sameNullness = sort != Sort.STRING
                        || arm.stringNullness.equals(nullness);
                if (sameValue && sameNullness) continue;
                value = "(ite " + selectors.get(index) + " "
                        + arm.text + " " + value + ")";
                if (sort == Sort.STRING) {
                    nullness = "(ite " + selectors.get(index) + " "
                            + arm.stringNullness + " " + nullness + ")";
                }
            }
            recordGuardedReadUse(readIdentity,
                    GuardedReadNaming.projectionIdentity(read), activation,
                    selectors);
            return Term.vm(value, sort,
                    JavaPrimitiveSmtSemantics.widthOfJavaType(
                            optionalString(read, "_java_type")), nullness, "");
        }

        /**
         * Retains the value already propagated to the target read. The graph
         * has no role in rebuilding this value; it only has to be mapped back
         * to the one exact live container which replay can update.
         */
        private void captureTargetGuardedRead(JsonObject read, Term value,
                                              String origin) {
            InitialContainerObservation.Read selected = null;
            String selectorIdentity = "";
            for (JsonElement element : array(read, "candidates")) {
                if (!element.isJsonObject()) {
                    targetContainerGaps.add(origin
                            + ":TARGET_MAP_CANDIDATE_NOT_OBJECT");
                    return;
                }
                JsonElement expression = element.getAsJsonObject()
                        .get("expression");
                InitialContainerObservation.Read candidate = expression != null
                        && expression.isJsonObject()
                        ? InitialContainerObservation.initialRead(
                        expression.getAsJsonObject()) : null;
                if (candidate == null
                        || !"ASSOCIATIVE".equals(candidate.shape)) {
                    targetContainerGaps.add(origin
                            + ":TARGET_MAP_INITIAL_READ_MISSING");
                    return;
                }
                String identity = targetSelectorIdentity(candidate);
                if (identity.isEmpty()) {
                    targetContainerGaps.add(origin
                            + ":TARGET_MAP_SELECTOR_UNREPLAYABLE");
                    return;
                }
                if (selected == null) {
                    selected = candidate;
                    selectorIdentity = identity;
                } else if (!selected.stateSymbol.equals(
                        candidate.stateSymbol)
                        || !selectorIdentity.equals(identity)
                        || !JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                        selected.javaType).equals(
                        JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                                candidate.javaType))) {
                    targetContainerGaps.add(origin
                            + ":TARGET_MAP_CANDIDATES_DISAGREE");
                    return;
                }
            }
            if (selected == null) {
                targetContainerGaps.add(origin
                        + ":TARGET_MAP_CANDIDATES_EMPTY");
                return;
            }
            recordTargetContainerRead(selected, selectorIdentity, value,
                    origin);
        }

        private String targetSelectorIdentity(
                InitialContainerObservation.Read read) {
            try {
                if (read.dynamicAssociativeSelector()) {
                    return "ACCESS:" + targetReadAnchors.contentAnchor(
                            read.selectorExpression);
                }
                if (read.selectorExpression != null) {
                    return "KEY:" + targetReadAnchors.contentAnchor(
                            read.selectorExpression);
                }
            } catch (IllegalArgumentException malformed) {
                return "";
            }
            if (!read.iterationProjection.isEmpty() && read.index != null) {
                return "ITERATION:" + read.iterationProjection + ':'
                        + read.index;
            }
            return read.index == null ? "" : "INDEX:" + read.index;
        }

        private void recordTargetContainerRead(
                InitialContainerObservation.Read read,
                String selectorIdentity, Term value, String origin) {
            if (!"ASSOCIATIVE".equals(read.shape)) {
                targetContainerGaps.add(origin
                        + ":TARGET_CONTAINER_SHAPE:" + read.shape);
                return;
            }
            if (value.sort != Sort.REF && value.sort != Sort.INT
                    && value.sort != Sort.BOOL) {
                targetContainerGaps.add(origin
                        + ":TARGET_CONTAINER_VALUE_SORT:" + value.sort);
                return;
            }
            String identity = read.shape + '\u0000' + read.stateSymbol
                    + '\u0000' + selectorIdentity;
            TargetContainerRead candidate = new TargetContainerRead(
                    identity, read, value);
            TargetContainerRead held = targetContainerReads.putIfAbsent(
                    identity, candidate);
            if (held != null && !held.sameValue(candidate)) {
                targetContainerGaps.add(origin
                        + ":TARGET_CONTAINER_VALUE_AMBIGUOUS");
            }
        }

        private void recordGuardedReadUse(String readIdentity,
                                          String projectionIdentity,
                                          String activation,
                                          Collection<String> selectors) {
            VmTermLowering.recordGuardedReadUse(guardedReadUses,
                    readIdentity, projectionIdentity, activation, selectors,
                    identity -> unsupported.add(
                            "GUARDED_READ_USE_AMBIGUOUS:" + identity));
        }

        private void noteReadFromWriterCase(JsonObject candidate,
                                            String readSelector,
                                            String origin) {
            String writerOwner = optionalString(candidate,
                    SymbolicPropagationClosure.WRITER_CASE_OWNER);
            String writerSelector = optionalString(candidate,
                    SymbolicPropagationClosure.WRITER_CASE_SELECTOR);
            JsonArray closure = array(candidate,
                    SymbolicPropagationClosure.WRITER_CASE_CLOSURE);
            boolean containsWriter = false;
            Set<String> identities = new LinkedHashSet<>();
            if (closure.size() == 0) {
                unsupported.add(origin
                        + ":READ_FROM_WRITER_CASE_UNRESOLVED:"
                        + optionalString(candidate, "selector"));
                return;
            }
            for (JsonElement encoded : closure) {
                if (!encoded.isJsonObject()) {
                    unsupported.add(origin
                            + ":READ_FROM_WRITER_CASE_UNRESOLVED:"
                            + optionalString(candidate, "selector"));
                    return;
                }
                JsonObject localCase = encoded.getAsJsonObject();
                String family = optionalString(localCase,
                        SymbolicPropagationClosure.WRITER_CASE_FAMILY);
                String owner = optionalString(localCase,
                        SymbolicPropagationClosure.WRITER_CASE_OWNER);
                String caseSelector = optionalString(localCase,
                        SymbolicPropagationClosure.WRITER_CASE_SELECTOR);
                String identity = family + "\n" + owner;
                if (family.isEmpty() || owner.isEmpty()
                        || !caseSelector.equals(
                        LocalCaseIdentity.selector(owner))
                        || !identities.add(identity)) {
                    unsupported.add(origin
                            + ":READ_FROM_WRITER_CASE_UNRESOLVED:"
                            + optionalString(candidate, "selector"));
                    return;
                }
                containsWriter |= owner.equals(writerOwner)
                        && caseSelector.equals(writerSelector);
                JsonElement pathGuard = owner.equals(writerOwner)
                        ? candidate.get("pathGuard")
                        : SharedStateEvidence.emptyConjunction();
                registerReadFromWriterCase(family, owner, caseSelector,
                        readSelector, pathGuard, origin, candidate);
            }
            if (!containsWriter) {
                unsupported.add(origin
                        + ":READ_FROM_WRITER_CASE_UNRESOLVED:"
                        + optionalString(candidate, "selector"));
            }
        }

        private void registerReadFromWriterCase(
                String family, String owner, String caseSelector,
                String readSelector, JsonElement pathGuard, String origin,
                JsonObject candidate) {
            usedConsumerFamilies.add(family);
            consumerFamilyActivations.computeIfAbsent(family,
                    ignored -> new LinkedHashSet<>()).add(readSelector);
            GuardedReadCaseBinding binding =
                    new GuardedReadCaseBinding(readSelector,
                            caseSelector, owner, pathGuard);
            Map<String, GuardedReadCaseBinding> bindings =
                    readFromWriterCases.computeIfAbsent(family,
                            ignored -> new LinkedHashMap<>());
            GuardedReadCaseBinding held = bindings.putIfAbsent(
                    binding.identity(), binding);
            if (held != null && !held.same(binding)) {
                unsupported.add(origin
                        + ":READ_FROM_WRITER_CASE_AMBIGUOUS:"
                        + optionalString(candidate, "selector"));
            }
        }

        private static String andGuard(String left, String right) {
            if (left == null || left.isEmpty() || "true".equals(left)) {
                return right == null || right.isEmpty() ? "true" : right;
            }
            if (right == null || right.isEmpty() || "true".equals(right)) {
                return left;
            }
            if (left.equals(right)) return left;
            return "(and " + left + " " + right + ")";
        }

        private void requireUnderCurrentGuard(String predicate) {
            assertions.add("true".equals(currentReadActivationGuard)
                    ? predicate : "(=> " + currentReadActivationGuard + " "
                    + predicate + ")");
        }

        private Term containerTerm(JsonObject expression, String origin) {
            ContainerSmtCodec.Term result = ContainerSmtCodec.term(
                    expression, containerHost(origin));
            Term value = fromContainerTerm(result, origin);
            if (captureTargetContainerReads && guardedReadDepth == 0
                    && value != null) {
                InitialContainerObservation.Read read =
                        InitialContainerObservation.initialRead(expression);
                if (read != null) {
                    String selector = targetSelectorIdentity(read);
                    if (selector.isEmpty()) {
                        targetContainerGaps.add(origin
                                + ":TARGET_CONTAINER_SELECTOR_UNREPLAYABLE");
                    } else {
                        recordTargetContainerRead(read, selector, value,
                                origin);
                    }
                }
            }
            return value;
        }

        private Term containerFieldTerm(
                JsonObject expression, String origin) {
            return fromContainerTerm(ContainerSmtCodec.field(
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
                    return new ContainerSmtCodec.Term(
                            (shape == ContainerSmtCodec.Sort.INDEXED
                                    ? "(indexed_state_of "
                                    : "(assoc_state_of ")
                                    + reference.text + ")", shape);
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
                    Sort nativeExpected = expected == ContainerSmtCodec.Sort.INT
                            ? Sort.INT
                            : expected == ContainerSmtCodec.Sort.BOOL
                            ? Sort.BOOL
                            : expected == ContainerSmtCodec.Sort.REF
                            ? Sort.REF
                            : expected == ContainerSmtCodec.Sort.INDEXED
                            ? Sort.ARRAY_VALUE
                            : expected == ContainerSmtCodec.Sort.ASSOCIATIVE
                            ? Sort.MAP : null;
                    return shareTerm(toContainerTerm(term(expression,
                            nativeExpected,
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
                    String valueText = value.text;
                    if (value.sort != Sort.STRING) {
                        ContainerSmtCodec.Term shared = shareTerm(
                                toContainerTerm(value));
                        if (shared != null) valueText = shared.text;
                    }
                    String integralValue = value.sort == Sort.INT
                            ? ContainerSmtCodec.boxIntegral(valueText,
                            VmTermLowering.expressionJavaType(expression)) : "";
                    String stringValue = "";
                    if (value.sort == Sort.STRING) {
                        if (value.stringNullness.isEmpty()) {
                            unsupported("ContainerStringNullness");
                            return null;
                        }
                        stringValue = "false".equals(
                                value.stringNullness)
                                ? "(VString " + value.text + ")"
                                : "(ite " + value.stringNullness
                                + " (VRef nullRef) (VString "
                                + value.text + "))";
                    }
                    String boxed = value.sort == Sort.INT
                            ? firstNonBlank(integralValue,
                            "(VInt " + valueText + ")")
                            : value.sort == Sort.BOOL
                            ? "(VBool " + valueText + ")"
                            : value.sort == Sort.REF
                            ? "(VRef " + valueText + ")"
                            : value.sort == Sort.STRING
                            ? stringValue
                            : value.sort == Sort.FLOAT32
                            ? "(VFloat " + valueText + ")"
                            : value.sort == Sort.FLOAT64
                            ? "(VDouble " + valueText + ")" : "";
                    if (boxed.isEmpty()) {
                        unsupported("ContainerBox:" + value.sort);
                        return null;
                    }
                    return shareTerm(new ContainerSmtCodec.Term(boxed,
                            ContainerSmtCodec.Sort.VALUE));
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
                    requireUnderCurrentGuard(predicate);
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

        /** Binds read choice only while a consumer expression is active. */
        private void finishGuardedReadSelections() {
            List<String> reads = new ArrayList<>(
                    guardedReadUses.keySet());
            Collections.sort(reads);
            for (String read : reads) {
                List<String> selectors = new ArrayList<>(
                        guardedReadSelectors.getOrDefault(read,
                                Collections.emptySet()));
                Collections.sort(selectors);
                if (selectors.isEmpty()) {
                    unsupported.add("GUARDED_READ_CHOICE_MISSING:" + read);
                    continue;
                }
                Map<String, GuardedReadUse> uses = guardedReadUses.get(read);
                if (uses == null || uses.isEmpty()) {
                    unsupported.add("GUARDED_READ_USE_MISSING:" + read);
                    continue;
                }
                List<String> useIds = new ArrayList<>(uses.keySet());
                Collections.sort(useIds);
                for (String useId : useIds) {
                    GuardedReadUse use = uses.get(useId);
                    assertions.add(ConcolicSmtComposer
                            .conditionalExactlyOne(use.activation,
                                    use.selectors));
                }
                Map<String, Set<String>> selectorGuards =
                        guardedSelectorActivationGuards.get(read);
                for (String selector : selectors) {
                    Set<String> guards = selectorGuards.get(selector);
                    if (guards == null || guards.isEmpty()) {
                        unsupported.add("GUARDED_READ_ARM_ACTIVATION_MISSING:"
                                + read + ":" + selector);
                        continue;
                    }
                    assertions.add("(=> " + selector + " "
                            + orTerms(new ArrayList<>(guards)) + ")");
                }
            }
        }

        /** Binds each captured value to its content-addressed live map. */
        private void bindTargetContainerReads(List<JsonObject> actions) {
            Map<String, Integer> dynamicByInput = new LinkedHashMap<>();
            for (TargetContainerRead read : targetContainerReads.values()) {
                JsonObject match = null;
                int matches = 0;
                for (JsonObject action : actions) {
                    if (!executable(action)
                            || !"BOUNDED_CONTAINER_STATE".equals(
                            optionalString(action, "symbolicDemand"))
                            || !read.stateSymbol.equals(
                            SharedStateEvidence.mapStateSymbolForAction(
                                    action))) {
                        continue;
                    }
                    matches++;
                    match = action;
                }
                if (matches != 1) {
                    targetContainerGaps.add(read.identity
                            + ":EXACT_MAP_ACTION_NOT_UNIQUE");
                    continue;
                }
                read.action = match;
                if (read.dynamic()) {
                    String input = optionalString(match, "symbol");
                    int count = dynamicByInput.getOrDefault(input, 0) + 1;
                    dynamicByInput.put(input, count);
                }
                String identity = read.identity + "\u0000"
                        + read.value.sort + "\u0000" + read.value.text;
                read.modelName = smtSymbols.mintFromDigest(
                        "container_target__", sha256(identity), identity, 16);
                if (read.value.sort == Sort.REF) {
                    read.nullModelName = read.modelName + "__is_null";
                    functionDeclarations.put(read.nullModelName,
                            "(define-fun " + read.nullModelName
                                    + " () Bool (= " + read.value.text
                                    + " nullRef))");
                    additionalModelNames.add(read.nullModelName);
                } else {
                    functionDeclarations.put(read.modelName,
                            "(define-fun " + read.modelName + " () "
                                    + read.value.sort.smt + " "
                                    + read.value.text + ")");
                    additionalModelNames.add(read.modelName);
                }
                targetContainerModels.add(read);
            }
            for (Map.Entry<String, Integer> entry
                    : dynamicByInput.entrySet()) {
                if (entry.getValue() > 1) {
                    targetContainerGaps.add(entry.getKey()
                            + ":MULTIPLE_TARGET_MAP_ACCESSES");
                }
            }
        }

        private void constrainIntegralInput(String name,
                                            String javaType, Sort sort) {
            if (sort != Sort.INT) return;
            JavaPrimitiveSmtSemantics.IntegralDomain domain =
                    JavaPrimitiveSmtSemantics.domainOfJavaType(javaType);
            if (domain == null) return;
            assertions.add("(and (<= " + domain.lower + " " + name
                    + ") (<= " + name + " " + domain.upper + "))");
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

        private Term constant(JsonObject expression, Sort expected,
                              String origin) {
            String raw = optionalString(expression, "_exp");
            String payload = constantPayload(raw);
            Sort sort = sortOfJava(optionalString(expression, "_java_type"));
            if (expected == Sort.BOOL && (sort == Sort.INT
                    || sort == Sort.BOOL)) {
                return Term.vm("0".equals(payload) ? "false" : "true",
                        Sort.BOOL);
            }
            if (expected == Sort.REF && ("0".equals(payload)
                    || VmExpressionIr.SYMBOLIC_NULL.equals(raw))) {
                return Term.vm("nullRef", Sort.REF);
            }
            if (sort == Sort.BOOL) {
                return Term.vm("0".equals(payload) ? "false" : "true",
                        Sort.BOOL);
            }
            if (sort == Sort.INT) {
                String literal = SmtModelValueCodec.integerLiteral(payload);
                if (literal == null) {
                    unsupported.add(origin + ":INVALID_INTEGER_LITERAL:"
                            + firstNonBlank(raw, "MISSING"));
                    return null;
                }
                return Term.vm(literal, Sort.INT,
                        JavaPrimitiveSmtSemantics.widthOfJavaType(
                                optionalString(expression, "_java_type")));
            }
            if (sort.floating()) {
                FloatingKind kind = floatingKind(sort);
                String literal = JavaPrimitiveSmtSemantics.floatingLiteral(
                        payload, kind);
                if (literal == null) {
                    unsupported.add(origin + ":INVALID_FLOATING_LITERAL:"
                            + firstNonBlank(raw, "MISSING"));
                    return null;
                }
                return Term.vm(literal, sort);
            }
            if (sort == Sort.STRING) {
                return Term.nonNullString(quote(payload), "true");
            }
            if (VmExpressionIr.SYMBOLIC_NULL.equals(raw)) {
                return Term.vm("nullRef", Sort.REF);
            }
            unsupported.add(origin + ":UNSUPPORTED_CONSTANT_TYPE:"
                    + firstNonBlank(optionalString(expression, "_java_type"),
                    "MISSING"));
            return null;
        }

        /** Lowers only casts whose value relation the SMT sorts preserve. */
        private Term typeCast(JsonObject expression, String origin) {
            return VmTermLowering.typeCast(this, expression, origin);
        }

        private Term binary(JsonObject expression, String origin) {
            String operator = JavaPrimitiveSmtSemantics.canonicalVmOperator(
                    optionalString(expression, "_op"));
            JsonElement leftExpression = expression.get("_left");
            if (leftExpression == null || leftExpression.isJsonNull()) {
                Term operand = term(expression.get("_right"), null,
                        origin + ":operand");
                if ("-".equals(operator) && operand != null
                        && numeric(operand.sort)) {
                    if (operand.sort.floating()) {
                        return Term.vm(JavaPrimitiveSmtSemantics
                                .floatingNegate(operand.text), operand.sort);
                    }
                    if (operand.integralWidth != IntegralWidth.NONE) {
                        return Term.vm(JavaPrimitiveSmtSemantics.wrap(
                                "(- " + operand.text + ")",
                                operand.integralWidth), Sort.INT,
                                operand.integralWidth);
                    }
                    unsupported.add(origin
                            + ":AMBIGUOUS_JAVA_INTEGRAL_UNARY_WIDTH");
                    return null;
                }
                if ("~".equals(operator) && operand != null
                        && operand.sort == Sort.INT
                        && operand.integralWidth != IntegralWidth.NONE) {
                    return Term.vm(JavaPrimitiveSmtSemantics.complement(
                            operand.text, operand.integralWidth), Sort.INT,
                            operand.integralWidth);
                }
                unsupported.add(origin + ":NON_NUMERIC_OR_UNKNOWN_UNARY:"
                        + firstNonBlank(operator, "MISSING"));
                return null;
            }
            Term left = term(expression.get("_left"), null,
                    origin + ":left");
            Term right = term(expression.get("_right"),
                    left == null ? null : left.sort, origin + ":right");
            if (left == null || right == null) return null;
            if (left.sort != right.sort && right.isZero()
                    && left.sort == Sort.REF) {
                right = Term.vm("nullRef", Sort.REF);
            } else if (left.sort != right.sort && left.isZero()
                    && right.sort == Sort.REF) {
                left = Term.vm("nullRef", Sort.REF);
            }
            if ("--".equals(operator)) {
                if (left.sort == Sort.INT && right.sort == Sort.INT
                        && left.integralWidth == IntegralWidth.JAVA_LONG
                        && right.integralWidth == IntegralWidth.JAVA_LONG) {
                    return Term.vm(JavaPrimitiveSmtSemantics
                            .integralCompareResult(left.text, right.text),
                            Sort.INT, IntegralWidth.JAVA_INT);
                }
                unsupported.add(origin + ":MALFORMED_JVM_LCMP_OPERANDS:"
                        + left.sort + ":" + left.integralWidth + ":"
                        + right.sort + ":" + right.integralWidth);
                return null;
            }
            if ("--l".equals(operator) || "--g".equals(operator)) {
                if (left.sort == right.sort && left.sort.floating()) {
                    return Term.vm(JavaPrimitiveSmtSemantics
                            .floatingCompareResult(left.text, right.text,
                                    "--g".equals(operator)), Sort.INT,
                            IntegralWidth.JAVA_INT);
                }
                unsupported.add(origin + ":MALFORMED_JVM_FP_CMP_OPERANDS:"
                        + operator + ":" + left.sort + ":" + right.sort);
                return null;
            }
            if (left.sort != right.sort && numeric(left.sort)
                    && numeric(right.sort)
                    && (left.sort.floating() || right.sort.floating())) {
                Sort promoted = left.sort == Sort.FLOAT64
                        || right.sort == Sort.FLOAT64
                        ? Sort.FLOAT64 : Sort.FLOAT32;
                left = floatingPromotion(left, promoted, origin + ":left");
                right = floatingPromotion(right, promoted,
                        origin + ":right");
                if (left == null || right == null) return null;
            }
            if ("==".equals(operator) || "!=".equals(operator)) {
                Term stringNullComparison = stringNullComparison(
                        left, right, operator);
                if (stringNullComparison != null) {
                    return stringNullComparison;
                }
                if (left.sort == Sort.STRING && right.sort == Sort.STRING) {
                    if (ContainerSmtCodec.handlesFieldBinding(expression)) {
                        Term symbol = ContainerSmtCodec.handlesField(
                                expression.get("_left")) ? right : left;
                        String materialization = ContainerSmtCodec
                                .materializedStringEquality(left.text,
                                right.text, symbol.stringNullness);
                        if (materialization.isEmpty()) {
                            unsupported.add(origin
                                    + ":STRING_MATERIALIZATION_NULLNESS");
                            return null;
                        }
                        return Term.vm(materialization, Sort.BOOL);
                    }
                    if (!left.stringReferenceOrigin.isEmpty()
                            && left.stringReferenceOrigin.equals(
                            right.stringReferenceOrigin)) {
                        return Term.vm("==".equals(operator)
                                ? "true" : "false", Sort.BOOL);
                    }
                    // A BinaryExpression over Java Strings comes from JVM
                    // reference comparison.  SMT string equality is content
                    unsupported.add(origin
                            + ":JAVA_STRING_REFERENCE_IDENTITY_"
                            + "MATERIALIZATION_UNMODELED");
                    return null;
                }
                if (left.sort != right.sort) {
                    unsupported.add(origin + ":SORT_MISMATCH:" + left.sort
                            + ":" + right.sort);
                    return null;
                }
                if (left.sort.floating()) {
                    return Term.vm(JavaPrimitiveSmtSemantics
                            .floatingComparison(operator, left.text,
                                    right.text), Sort.BOOL);
                }
                String equals = "(= " + left.text + " " + right.text + ")";
                return Term.vm("!=".equals(operator)
                        ? "(not " + equals + ")" : equals, Sort.BOOL);
            }
            if ("&&".equals(operator) || "||".equals(operator)) {
                if (left.sort != Sort.BOOL || right.sort != Sort.BOOL) {
                    unsupported.add(origin + ":NON_BOOLEAN_LOGIC");
                    return null;
                }
                return Term.vm("(" + ("&&".equals(operator) ? "and" : "or")
                        + " " + left.text + " " + right.text + ")",
                        Sort.BOOL);
            }
            String comparison = comparison(operator);
            if (!comparison.isEmpty()) {
                if (!numeric(left.sort) || !numeric(right.sort)) {
                    unsupported.add(origin + ":NON_NUMERIC_COMPARISON");
                    return null;
                }
                if (left.sort != right.sort) {
                    unsupported.add(origin + ":NUMERIC_SORT_MISMATCH:"
                            + left.sort + ":" + right.sort);
                    return null;
                }
                if (left.sort.floating()) {
                    return Term.vm(JavaPrimitiveSmtSemantics
                            .floatingComparison(operator, left.text,
                                    right.text), Sort.BOOL);
                }
                return Term.vm("(" + comparison + " " + left.text + " "
                        + right.text + ")", Sort.BOOL);
            }
            if (bitwiseOperator(operator)) {
                if (left.sort != Sort.INT || right.sort != Sort.INT) {
                    unsupported.add(origin + ":NON_INTEGRAL_BITWISE");
                    return null;
                }
                IntegralWidth width = JavaPrimitiveSmtSemantics.promote(
                        left.integralWidth, right.integralWidth);
                if (width == IntegralWidth.NONE) {
                    unsupported.add(origin
                            + ":AMBIGUOUS_JAVA_INTEGRAL_BITWISE_WIDTH:"
                            + operator + ":" + left.integralWidth + ":"
                            + right.integralWidth);
                    return null;
                }
                return Term.vm(JavaPrimitiveSmtSemantics.bitwise(operator,
                        left.text, right.text, width), Sort.INT, width);
            }
            if (shiftOperator(operator)) {
                if (left.sort != Sort.INT || right.sort != Sort.INT
                        || left.integralWidth == IntegralWidth.NONE) {
                    unsupported.add(origin
                            + ":AMBIGUOUS_JAVA_INTEGRAL_SHIFT:"
                            + operator + ":" + left.integralWidth + ":"
                            + right.integralWidth);
                    return null;
                }
                return Term.vm(JavaPrimitiveSmtSemantics.shift(operator,
                        left.text, right.text, left.integralWidth), Sort.INT,
                        left.integralWidth);
            }
            if (arithmeticOperator(operator)) {
                if (!numeric(left.sort) || !numeric(right.sort)) {
                    unsupported.add(origin + ":NON_NUMERIC_ARITHMETIC");
                    return null;
                }
                if (left.sort != right.sort) {
                    unsupported.add(origin + ":NUMERIC_SORT_MISMATCH:"
                            + left.sort + ":" + right.sort);
                    return null;
                }
                Sort result = left.sort;
                if ("%".equals(operator)) {
                    if (result.floating()) {
                        unsupported.add(origin
                                + ":JAVA_FLOATING_REMAINDER_UNMODELED");
                        return null;
                    }
                    IntegralWidth resultWidth = JavaPrimitiveSmtSemantics
                            .promote(left.integralWidth,
                                    right.integralWidth);
                    if (resultWidth == IntegralWidth.NONE) {
                        unsupported.add(origin
                                + ":AMBIGUOUS_JAVA_INTEGRAL_BINARY_WIDTH:"
                                + operator + ":" + left.integralWidth + ":"
                                + right.integralWidth);
                        return null;
                    }
                    assertions.add(JavaPrimitiveSmtSemantics
                            .integralDivisorDefined(right.text));
                    return Term.vm(JavaPrimitiveSmtSemantics
                            .integralRemainder(left.text, right.text,
                                    resultWidth), Sort.INT, resultWidth);
                }
                if (result.floating()) {
                    String arithmetic = JavaPrimitiveSmtSemantics
                            .floatingArithmetic(operator, left.text,
                                    right.text);
                    if (arithmetic != null) {
                        return Term.vm(arithmetic, result);
                    }
                    unsupported.add(origin
                            + ":JAVA_FLOATING_OPERATOR_UNMODELED:"
                            + operator);
                    return null;
                }
                if ("@".equals(operator) || "/".equals(operator)) {
                    unsupported.add(origin
                            + ":JAVA_INTEGRAL_DIVISION_UNMODELED");
                    return null;
                }
                String arithmetic = arithmetic(operator);
                String arithmeticExpression = "(" + arithmetic + " "
                        + left.text + " " + right.text + ")";
                IntegralWidth resultWidth = JavaPrimitiveSmtSemantics
                        .promote(left.integralWidth, right.integralWidth);
                if (resultWidth == IntegralWidth.NONE) {
                    unsupported.add(origin
                            + ":AMBIGUOUS_JAVA_INTEGRAL_BINARY_WIDTH:"
                            + operator + ":" + left.integralWidth + ":"
                            + right.integralWidth);
                    return null;
                }
                return Term.vm(JavaPrimitiveSmtSemantics.wrap(
                        arithmeticExpression, resultWidth), Sort.INT,
                        resultWidth);
            }
            unsupported.add(origin + ":BINARY_OPERATOR:" + operator);
            return null;
        }

        /**
         * Lowers the Java reference-null view of a String without confusing
         * it with the empty string.
         */
        private Term stringNullComparison(Term left, Term right,
                                          String operator) {
            Term string = null;
            if (left.sort == Sort.STRING && right.isNullReference()) {
                string = left;
            } else if (right.sort == Sort.STRING
                    && left.isNullReference()) {
                string = right;
            }
            if (string == null || string.stringNullness.isEmpty()) {
                return null;
            }
            String isNull = string.stringNullness;
            return Term.vm("!=".equals(operator)
                    ? "(not " + isNull + ")" : isNull, Sort.BOOL);
        }

        private Term floatingPromotion(Term term, Sort target,
                                       String origin) {
            return VmTermLowering.floatingPromotion(this, term, target,
                    origin);
        }

        private Term stringOperation(JsonObject expression, String origin) {
            String operation = optionalString(expression, "_name");
            JsonArray parameters = array(expression, "_param_list");
            boolean negated = optionalBool(expression, "_is_not", false);
            if ("isEmpty".equals(operation)) {
                List<Term> strings = stringParameters(parameters, 1, origin,
                        operation);
                if (strings == null) return null;
                Term receiver = strings.get(0);
                if (!requireNonNullStrings(strings, origin, operation)) {
                    return null;
                }
                return booleanStringResult("(= (str.len " + receiver.text
                        + ") 0)", negated);
            }
            if ("length".equals(operation)) {
                if (negated) {
                    unsupported.add(origin + ":NEGATED_STRING_VALUE_"
                            + "OPERATION:length");
                    return null;
                }
                List<Term> strings = stringParameters(parameters, 1, origin,
                        operation);
                if (strings == null) return null;
                if (!requireNonNullStrings(strings, origin, operation)) {
                    return null;
                }
                Term length = Term.vm("(str.len "
                        + strings.get(0).text + ")", Sort.INT,
                        IntegralWidth.JAVA_INT);
                JavaPrimitiveSmtSemantics.IntegralDomain intDomain =
                        JavaPrimitiveSmtSemantics.domainOfJavaType("I");
                assertions.add("(and (<= " + intDomain.lower + " "
                        + length.text + ") (<= " + length.text + " "
                        + intDomain.upper + "))");
                return length;
            }
            if ("concat".equals(operation)) {
                if (negated) {
                    unsupported.add(origin + ":NEGATED_STRING_VALUE_"
                            + "OPERATION:concat");
                    return null;
                }
                if (parameters.size() < 1) {
                    unsupported.add(origin + ":STRING_CONCAT_ARITY:"
                            + parameters.size());
                    return null;
                }
                List<Term> strings = stringParameters(parameters,
                        parameters.size(), origin, operation);
                if (strings == null) return null;
                if (!requireNonNullStrings(strings, origin, operation)) {
                    return null;
                }
                if (strings.size() == 1) {
                    return Term.nonNullString(strings.get(0).text, "true");
                }
                StringBuilder result = new StringBuilder("(str.++");
                for (Term value : strings) {
                    result.append(' ').append(value.text);
                }
                return Term.nonNullString(result.append(')').toString(),
                        "true");
            }
            if ("toString".equals(operation)) {
                if (negated) {
                    return codecGap("OpStrExpression.toString",
                            "NEGATED_VALUE_OPERATION", origin);
                }
                if (parameters.size() != 1
                        || !isPrimitiveIntExpression(parameters.get(0))) {
                    return codecGap("OpStrExpression.toString",
                            "REQUIRES_ONE_PRIMITIVE_INT", origin);
                }
                Term integer = term(parameters.get(0), Sort.INT,
                        origin + ":toString");
                if (integer == null || integer.sort != Sort.INT) {
                    return codecGap("OpStrExpression.toString",
                            "NON_INT_TERM", origin);
                }
                assertJavaIntRange(integer);
                return javaIntString(integer);
            }
            if ("equals".equals(operation)) {
                return stringEquals(parameters, origin, negated);
            }
            if (!("contains".equals(operation)
                    || "startsWith".equals(operation)
                    || "endsWith".equals(operation))) {
                unsupported.add(origin + ":OP_STRING_OPERATOR:"
                        + firstNonBlank(operation, "MISSING"));
                return null;
            }
            List<Term> strings = stringParameters(parameters, 2, origin,
                    operation);
            if (strings == null) return null;
            if (!requireNonNullStrings(strings, origin, operation)) {
                return null;
            }
            Term receiver = strings.get(0);
            Term argument = strings.get(1);
            String predicate;
            if ("contains".equals(operation)) {
                predicate = "(str.contains " + receiver.text + " "
                        + argument.text + ")";
            } else if ("startsWith".equals(operation)) {
                predicate = "(str.prefixof " + argument.text + " "
                        + receiver.text + ")";
            } else {
                predicate = "(str.suffixof " + argument.text + " "
                        + receiver.text + ")";
            }
            return booleanStringResult(predicate, negated);
        }

        /** Java String.equals requires a non-null receiver but accepts null. */
        private Term stringEquals(JsonArray parameters, String origin,
                                  boolean negated) {
            if (parameters.size() != 2) {
                unsupported.add(origin + ":STRING_EQUALS_ARITY:"
                        + parameters.size());
                return null;
            }
            Term receiver = term(parameters.get(0), null,
                    origin + ":equals:parameter0");
            Term argument = term(parameters.get(1), null,
                    origin + ":equals:parameter1");
            if (receiver == null || argument == null) return null;
            if (receiver.sort != Sort.STRING) {
                unsupported.add(origin
                        + ":STRING_EQUALS_SORT_MISMATCH:0:"
                        + receiver.sort);
                return null;
            }
            if (!requireNonNullString(receiver, origin, "equals", 0)) {
                return null;
            }
            String predicate;
            if (argument.isNullReference()) {
                predicate = "false";
            } else if (argument.sort == Sort.STRING) {
                if (argument.stringNullness.isEmpty()) {
                    unsupported.add(origin
                            + ":STRING_EQUALS_NULLABILITY_UNKNOWN:1");
                    return null;
                }
                String contentEquals = "(= " + receiver.text + " "
                        + argument.text + ")";
                predicate = "false".equals(argument.stringNullness)
                        ? contentEquals : "(and (not "
                        + argument.stringNullness + ") "
                        + contentEquals + ")";
            } else {
                unsupported.add(origin
                        + ":STRING_EQUALS_SORT_MISMATCH:1:"
                        + argument.sort);
                return null;
            }
            return booleanStringResult(predicate, negated);
        }

        private List<Term> stringParameters(JsonArray parameters,
                                            int expectedArity,
                                            String origin,
                                            String operation) {
            if (parameters.size() != expectedArity) {
                unsupported.add(origin + ":STRING_"
                        + operation.toUpperCase(java.util.Locale.ROOT)
                        + "_ARITY:" + parameters.size());
                return null;
            }
            List<Term> result = new ArrayList<>();
            for (int index = 0; index < parameters.size(); index++) {
                // Do not pass STRING as an expected sort here. Symbol terms
                // use that hint when choosing their declaration sort, which
                Term value = term(parameters.get(index), null,
                        origin + ":" + operation + ":parameter" + index);
                if (value == null) return null;
                if (value.sort != Sort.STRING) {
                    unsupported.add(origin + ":STRING_"
                            + operation.toUpperCase(java.util.Locale.ROOT)
                            + "_SORT_MISMATCH:" + index + ":" + value.sort);
                    return null;
                }
                result.add(value);
            }
            return result;
        }

        private boolean requireNonNullStrings(List<Term> strings,
                                              String origin,
                                              String operation) {
            for (int index = 0; index < strings.size(); index++) {
                if (!requireNonNullString(strings.get(index), origin,
                        operation, index)) return false;
            }
            return true;
        }

        /**
         * Evaluation of an instance String operation proves its receiver was
         * non-null, so the query may assert it; unknown nullability refuses.
         */
        private boolean requireNonNullString(Term value, String origin,
                                             String operation, int index) {
            if (value.stringNullness.isEmpty()) {
                unsupported.add(origin + ":STRING_"
                        + operation.toUpperCase(java.util.Locale.ROOT)
                        + "_NULLABILITY_UNKNOWN:" + index);
                return false;
            }
            if (!"false".equals(value.stringNullness)) {
                requireUnderCurrentGuard(
                        "(not " + value.stringNullness + ")");
            }
            return true;
        }

        private Term booleanStringResult(String predicate,
                                         boolean negated) {
            return VmTermLowering.booleanStringResult(predicate, negated,
                    "true");
        }

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

        private Term methodTerm(JsonObject expression, String origin) {
            String method = firstNonBlank(optionalString(expression, "_name"),
                    "unknown_method");
            // splitElement and parseInt carry the same structural round-trip
            // semantics the composition encoder proves; this mirrors
            if (isJavaParseInt(method)) {
                return parseIntTerm(expression, origin);
            }
            if (isJavaSplitElement(method)) {
                return splitElementTerm(expression, origin);
            }
            unsupported.add(origin + ":METHOD_SEMANTICS_MISSING:" + method);
            return null;
        }

        /** Mirror of {@link ConcolicSmtComposer}'s {@code parseIntTerm}. */
        private Term parseIntTerm(JsonObject expression, String origin) {
            return VmTermLowering.parseIntTerm(this, expression, origin);
        }

        /** Mirror of {@link ConcolicSmtComposer}'s {@code splitElementTerm}. */
        private Term splitElementTerm(JsonObject expression, String origin) {
            SplitPrefix match = exactSplitPrefix(expression);
            if (!match.complete()) {
                return codecGap("java/lang/String.splitElement", match.gap,
                        origin);
            }
            Term integer = term(match.integerExpression, Sort.INT,
                    origin + ":splitElement");
            if (integer == null || integer.sort != Sort.INT) {
                return codecGap("java/lang/String.splitElement",
                        "ROUNDTRIP_SOURCE_NOT_INT", origin);
            }
            assertJavaIntRange(integer);
            return javaIntString(integer);
        }

        private Term codecGap(String operation, String gap, String origin) {
            return VmTermLowering.codecGap(this, operation, gap, origin,
                    null);
        }

        /**
         * Mirror of {@link ConcolicSmtComposer}'s {@code exactSplitPrefix}.
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
            String delimiterGap = decimalDelimiterGap(delimiter);
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

        private String decimalDelimiterGap(String value) {
            if (value == null || value.length() != 1) {
                return "REGEX_NOT_SAFE_SINGLE_LITERAL";
            }
            char delimiter = value.charAt(0);
            if (Character.isISOControl(delimiter)) {
                return "REGEX_NOT_SAFE_SINGLE_LITERAL";
            }
            if ("\\.^$|?*+()[]{}".indexOf(delimiter) >= 0) {
                return "REGEX_NOT_SAFE_SINGLE_LITERAL";
            }
            if (Character.isDigit(delimiter) || delimiter == '-') {
                return "DELIMITER_OCCURS_IN_JAVA_INT_TEXT";
            }
            return "";
        }

        private Term javaIntString(Term integer) {
            usesJavaIntString = true;
            return VmTermLowering.javaIntString(integer);
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
            modelNames.addAll(additionalModelNames);
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

    private static final class GuardedReadCaseBinding {
        private final String readSelector;
        private final String caseSelector;
        private final String owner;
        private final JsonElement pathGuard;

        private GuardedReadCaseBinding(String readSelector,
                                          String caseSelector,
                                          String owner,
                                          JsonElement pathGuard) {
            this.readSelector = readSelector;
            this.caseSelector = caseSelector;
            this.owner = owner;
            this.pathGuard = pathGuard;
        }

        private String identity() {
            return readSelector + "\n" + caseSelector;
        }

        private boolean same(GuardedReadCaseBinding other) {
            return other != null && readSelector.equals(other.readSelector)
                    && caseSelector.equals(other.caseSelector)
                    && owner.equals(other.owner);
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

    /** One exact target-side container value already computed by propagation. */
    private static final class TargetContainerRead {
        private final String identity;
        private final String stateSymbol;
        private final Integer index;
        private final JsonObject selector;
        private final String iterationProjection;
        private final boolean dynamic;
        private final Term value;
        private JsonObject action;
        private String modelName = "";
        private String nullModelName = "";

        private TargetContainerRead(String identity,
                                    InitialContainerObservation.Read read,
                                    Term value) {
            this.identity = identity;
            this.stateSymbol = read.stateSymbol;
            this.index = read.index;
            this.selector = read.selector;
            this.iterationProjection = read.iterationProjection;
            this.dynamic = read.dynamicAssociativeSelector();
            this.value = value;
        }

        private boolean dynamic() {
            return dynamic;
        }

        private boolean sameValue(TargetContainerRead other) {
            return other != null && value.sort == other.value.sort
                    && value.text.equals(other.value.text);
        }

        private boolean addTarget(JsonObject target, int occurrence) {
            target.addProperty("shape", "ASSOCIATIVE");
            if (dynamic) {
                if (occurrence < 1) return false;
                target.addProperty("selectorKind", "ACCESS_ORDINAL");
                target.addProperty("accessOrdinal", occurrence);
                return true;
            }
            if (!iterationProjection.isEmpty()) {
                if (index == null || index < 0) return false;
                target.addProperty("selectorKind", "ITERATION_INDEX");
                target.addProperty("index", index);
                target.addProperty("projection", iterationProjection);
                return true;
            }
            if (selector == null) return false;
            String keyType = optionalString(selector, "_java_type");
            String keyValue = constantPayload(optionalString(selector, "_exp"));
            if (keyType.isEmpty() || keyValue.isEmpty()) return false;
            target.addProperty("keyJavaType", keyType);
            target.addProperty("keyValue", keyValue);
            return true;
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

    /** Projects only the final target value; its SMT term already contains
     * the complete propagated map history and guarded case selection. */
    private static ModelProjection targetContainerAssignments(
            Encoder encoder, Map<String, String> values,
            int targetOccurrence) {
        JsonArray result = new JsonArray();
        Set<String> unresolved = new LinkedHashSet<>();
        for (TargetContainerRead read : encoder.targetContainerModels) {
            String modelName = read.value.sort == Sort.REF
                    ? read.nullModelName : read.modelName;
            String modeled = values.get(modelName);
            if (modeled == null || read.action == null) {
                unresolved.add(modelName);
                continue;
            }
            String valueType;
            String value = "";
            boolean modelIsNull = false;
            if (read.value.sort == Sort.REF) {
                if ("true".equals(modeled)) {
                    valueType = "NULL";
                    value = "null";
                    modelIsNull = true;
                } else if ("false".equals(modeled)) {
                    // The branch only constrains non-nullness. Keep the live
                    // reference rather than inventing an object identity.
                    valueType = "UNCHANGED";
                } else {
                    unresolved.add(modelName);
                    continue;
                }
            } else if (read.value.sort == Sort.INT
                    || read.value.sort == Sort.BOOL) {
                valueType = read.value.sort.replayName();
                value = SmtModelValueCodec.normalizeScalar(modeled);
            } else {
                unresolved.add(modelName);
                continue;
            }
            JsonObject target = new JsonObject();
            if (!read.addTarget(target, targetOccurrence)) {
                unresolved.add(modelName);
                continue;
            }
            JsonObject assignment = new JsonObject();
            assignment.addProperty("modelAssignmentKey", modelName);
            assignment.addProperty("engineSymbol", modelName);
            assignment.addProperty("inputSymbol",
                    optionalString(read.action, "symbol"));
            assignment.addProperty("valueType", valueType);
            if (!value.isEmpty()) assignment.addProperty("value", value);
            if (modelIsNull) assignment.addProperty("modelIsNull", true);
            assignment.add("containerTarget", target);
            result.add(assignment);
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
        private final JsonArray consumerAnchorCaseDependencies;
        private final String sourceActivationOccurrenceId;

        private PathQuery(String queryKey,
                          BranchReplayContract replayContract,
                          SolverPathContext pathContext,
                          JsonArray consumerAnchorCaseDependencies,
                          String sourceActivationOccurrenceId) {
            this.queryKey = queryKey;
            this.replayContract = replayContract;
            this.pathContext = pathContext;
            // SharedExpressionTable.expand() has already reconstructed one
            // immutable expression DAG for this worker.  This array is only
            // read during solving; a defensive deep copy would recursively
            // expand the DAG once more before Z3 is even started.
            this.consumerAnchorCaseDependencies =
                    consumerAnchorCaseDependencies;
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
                        array(task,
                                LinkedReplayBundle.CASE_DEPENDENCIES_FIELD),
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
                if (selected != null) return null;
                selected = new ConfiguredSourceMatch(phase.phaseId(),
                        phase.sourceId(), field.signature());
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
            boolean registered = names != null
                    && (configuredSourceResolution(symbol,
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

    /** Mirror of {@link ConcolicSmtComposer}'s {@code SplitPrefix}. */
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

    private static Sort castSort(String descriptor) {
        return sortOfJava(descriptor);
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
