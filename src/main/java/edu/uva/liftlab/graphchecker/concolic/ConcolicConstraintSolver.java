package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.IntegralWidth;
import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.FloatingKind;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;

import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sha256;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.requiredObject;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Solves one canonical path flip and maps its model to real input actions. */
public final class ConcolicConstraintSolver {
    private ConcolicConstraintSolver() {
    }

    public static Result solve(JsonObject task, JsonObject activation,
                               Path z3, long timeoutMillis)
            throws IOException, InterruptedException {
        PathQuery query = PathQuery.decode(task);
        BranchReplayContract replayContract = query.replayContract;
        JsonArray branchConstraints = replayContract
                .requiredPathPredicates();
        JsonArray contextConstraints = query.pathContext.expressions();
        List<JsonObject> actions = materializationActions(activation);
        boolean targetReachQuery = targetReachQuery(task);
        TargetReplaySupportPlan targetReplayPlan = targetReachQuery
                ? TargetReplaySupportPlan.build(task, activation,
                branchConstraints, contextConstraints, actions)
                : TargetReplaySupportPlan.notTarget();
        SparseContainerBoundaries containerBoundaries =
                SparseContainerBoundaries.discover(
                        branchConstraints, contextConstraints, actions);
        Encoder encoder = new Encoder(containerBoundaries);
        for (int index = 0; index < contextConstraints.size(); index++) {
            JsonElement constraint = contextConstraints.get(index);
            if (!containerBoundaries.isConcreteObservation(constraint)) {
                encoder.addConstraint(constraint, "q_context_" + index);
            }
        }
        List<Set<String>> branchSymbolSets = new ArrayList<>();
        Set<String> targetSymbols = new LinkedHashSet<>();
        for (int index = 0; index < branchConstraints.size(); index++) {
            if (targetReachQuery
                    && targetReplayPlan.isExternalCompanion(index)) {
                // This witnessed predecessor is fixed by the full-session
                // replay's exact RPC/shared-state companion.  It remains in
                // BranchReplayContract for runtime prefix validation, but no
                // unconstrained remote source is introduced into the local
                // flip SMT query.
                branchSymbolSets.add(Collections.<String>emptySet());
                continue;
            }
            Set<String> symbols = encoder.addConstraint(
                    branchConstraints.get(index),
                    "q_branch_" + index);
            branchSymbolSets.add(symbols);
            if (index + 1 == branchConstraints.size()) {
                targetSymbols.addAll(symbols);
            }
        }
        ReplaySupport targetSupport = classifyReplaySupport(
                encoder, targetSymbols, actions, activation);
        ReplaySupport replaySupport = classifyReplaySupport(
                encoder, replayControlFrontier(branchSymbolSets),
                actions, activation);
        Set<String> writableReplayControlSymbols =
                replaySupport.writableSymbols;
        Set<String> nullableReplaySymbols = referencesComparedWithNull(
                branchConstraints);
        for (String alias : new ArrayList<>(nullableReplaySymbols)) {
            String representative = encoder
                    .materializableFieldRepresentative(
                            alias, actions, activation);
            if (representative != null) {
                nullableReplaySymbols.add(representative);
            }
        }
        ReferenceDomains referenceDomains = encoder.bindReferenceDomains(
                writableReplayControlSymbols, actions,
                nullableReplaySymbols);
        encoder.bindSparseContainerBoundaries();
        encoder.bindRecordedReadCut(query.recordedReadCut);
        String smt = encoder.finish();
        JsonObject record = baseRecord(query.queryKey);
        record.add("unsupported", strings(encoder.unsupported));
        if (!encoder.unsupported.isEmpty()) {
            record.addProperty("status", "UNSUPPORTED");
            record.addProperty("reason", "UNSUPPORTED_EXPRESSION_IR");
            return new Result(record, smt, new JsonArray(),
                    replayContract);
        }

        if (!containerBoundaries.gaps.isEmpty()) {
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason",
                    "SPARSE_CONTAINER_BOUNDARY_IS_NOT_MATERIALIZABLE");
            record.add("unresolvedContainerBoundaries",
                    strings(containerBoundaries.gaps));
            return new Result(record, smt, new JsonArray(),
                    replayContract);
        }

        if (targetReachQuery && targetReplayPlan.hasGap()) {
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason", targetReplayPlan.reason());
            record.add("unresolvedCompanionSupportSymbols",
                    strings(targetReplayPlan.gapSymbols()));
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
        // Which writer the model chose is part of the model, not a footnote
        // to it: without reading the selectors back, a replay could not know
        // which read-from arm it is supposed to confirm.
        SelectedReadCut readCut = SelectedReadCut.of(query.recordedReadCut,
                values);
        if (!readCut.isEmpty()) {
            record.add("selectedReadCut", readCut.toJson());
        }
        // The SMT model satisfies the complete required prefix plus target.
        // Every writable root in that conjunction must therefore be replayed
        // from the same model. A derived field alias is represented by the
        // unique writable root that the recorded field bindings equate with
        // it. Free environment support was refused above; sparse container
        // values are projected by their dedicated path below.
        ModelProjection projection = modelAssignments(encoder, values,
                actions, activation, writableReplayControlSymbols,
                referenceDomains);
        ModelProjection containerProjection =
                sparseContainerAssignments(values, containerBoundaries,
                        referenceDomains,
                        replayContract.source().occurrence());
        for (JsonElement assignment : containerProjection.assignments) {
            projection.assignments.add(assignment);
        }
        projection.unresolved.addAll(containerProjection.unresolved);
        JsonArray assignments = projection.assignments;
        if (writableReplayControlSymbols.isEmpty()
                && containerBoundaries.models.isEmpty()) {
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
        return new Result(record, smt, assignments, replayContract, readCut);
    }

    public static final class Result {
        public final JsonObject record;
        public final String smtLib;
        public final JsonArray modelAssignments;
        final BranchReplayContract replayContract;
        /** The read-from arms this model selected, if it selected any. */
        final SelectedReadCut readCut;

        private Result(JsonObject record, String smtLib,
                       JsonArray modelAssignments,
                       BranchReplayContract replayContract) {
            this(record, smtLib, modelAssignments, replayContract,
                    SelectedReadCut.none());
        }

        private Result(JsonObject record, String smtLib,
                       JsonArray modelAssignments,
                       BranchReplayContract replayContract,
                       SelectedReadCut readCut) {
            this.record = record;
            this.smtLib = smtLib;
            this.modelAssignments = modelAssignments;
            this.replayContract = replayContract;
            this.readCut = readCut;
        }
    }

    private static final class Encoder {
        private final SparseContainerBoundaries containerBoundaries;
        private final Map<String, Sort> declarations = new LinkedHashMap<>();
        private final Map<String, String> functionDeclarations =
                new LinkedHashMap<>();
        private final Map<String, SymbolNames> names =
                new LinkedHashMap<>();
        private final Map<String, String> containerStates =
                new LinkedHashMap<>();
        private final Map<String, Set<String>> fieldSymbols =
                new LinkedHashMap<>();
        private final List<String> assertions = new ArrayList<>();
        private final Set<String> unsupported = new LinkedHashSet<>();
        private final Set<String> controlledSymbols = new LinkedHashSet<>();
        private final Set<String> additionalModelNames =
                new LinkedHashSet<>();
        private final Set<String> javaIntRangeAssertions =
                new LinkedHashSet<>();
        private boolean usesJavaIntString;
        private Set<String> currentConstraintSymbols;

        private Encoder(SparseContainerBoundaries containerBoundaries) {
            this.containerBoundaries = containerBoundaries;
        }

        private Set<String> addConstraint(
                JsonElement expression, String origin) {
            currentConstraintSymbols = new LinkedHashSet<>();
            if (expression == null || !expression.isJsonObject()) {
                unsupported.add(origin + ":NON_OBJECT_EXPRESSION");
            } else {
                JsonObject object = expression.getAsJsonObject();
                String type = string(object, "_type");
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
            String type = string(object, "_type");
            if ("SymbolExpression".equals(type)) {
                return symbol(object, origin);
            }
            if ("ConstExpr".equals(type)
                    || "ConSymbolExp".equals(type)
                    || "ConStringSymbolExp".equals(type)) {
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
                return new Term("(not " + operand.text + ")", Sort.BOOL);
            }
            if ("TypeCastExpression".equals(type)) {
                return typeCast(object, origin);
            }
            if ("MethodExpression".equals(type)) {
                return methodTerm(object, origin);
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

        private Term containerTerm(JsonObject expression, String origin) {
            SparseContainerBoundary dynamic = containerBoundaries
                    .dynamicAssociativeBoundary(expression);
            if (dynamic != null) {
                Sort sort = sortOfJava(dynamic.javaType);
                if (sort != Sort.INT && sort != Sort.BOOL
                        && sort != Sort.REF) {
                    unsupported.add(origin
                            + ":UNSUPPORTED_DYNAMIC_CONTAINER_READ_SORT:"
                            + sort);
                    return null;
                }
                String name = "container_access__"
                        + sha256(dynamic.identity()).substring(0, 16);
                declarations.put(name, sort);
                Term term = new Term(name, sort,
                        JavaPrimitiveSmtSemantics.widthOfJavaType(
                                dynamic.javaType));
                containerBoundaries.record(dynamic, term);
                return term;
            }
            ContainerSmtCodec.Term result = ContainerSmtCodec.term(
                    expression, containerHost(origin));
            containerBoundaries.record(expression, result);
            return fromContainerTerm(result, origin);
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
                            ? Sort.INDEXED : Sort.ASSOCIATIVE;
                    if (identity != null && identity.isJsonObject()
                            && "SymbolExpression".equals(string(
                            identity.getAsJsonObject(), "_type"))) {
                        String raw = string(identity.getAsJsonObject(), "_exp");
                        if (raw.isEmpty()) {
                            unsupported("ContainerStateIdentity:" + shape);
                            return null;
                        }
                        String key = shape + "\u0000" + raw;
                        String name = containerStates.get(key);
                        if (name == null) {
                            name = "container__" + safeName(raw) + "__"
                                    + sha256(key).substring(0, 10);
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
                        ContainerSmtCodec.Term result =
                                ContainerSmtCodec.term(relation, this);
                        containerBoundaries.record(relation, result);
                        return result;
                    }
                    if (ContainerSmtCodec.handlesField(expression)) {
                        return ContainerSmtCodec.field(
                                expression.getAsJsonObject(), this);
                    }
                    Sort nativeExpected = expected == ContainerSmtCodec.Sort.INT
                            ? Sort.INT
                            : expected == ContainerSmtCodec.Sort.BOOL
                            ? Sort.BOOL
                            : expected == ContainerSmtCodec.Sort.REF
                            ? Sort.REF
                            : expected == ContainerSmtCodec.Sort.INDEXED
                            ? Sort.INDEXED
                            : expected == ContainerSmtCodec.Sort.ASSOCIATIVE
                            ? Sort.ASSOCIATIVE : null;
                    return toContainerTerm(term(expression, nativeExpected,
                            origin + ":container-operand"));
                }

                @Override
                public ContainerSmtCodec.Term box(JsonElement expression) {
                    Term value = term(expression, null,
                            origin + ":container-value");
                    if (value == null) return null;
                    String integralValue = value.sort == Sort.INT
                            ? ContainerSmtCodec.boxIntegral(value.text,
                            expressionJavaType(expression)) : "";
                    String stringValue = "";
                    if (value.sort == Sort.STRING) {
                        if (value.stringNullnessText.isEmpty()) {
                            unsupported("ContainerStringNullness");
                            return null;
                        }
                        stringValue = "false".equals(
                                value.stringNullnessText)
                                ? "(VString " + value.text + ")"
                                : "(ite " + value.stringNullnessText
                                + " (VRef nullRef) (VString "
                                + value.text + "))";
                    }
                    String boxed = value.sort == Sort.INT
                            ? firstNonBlank(integralValue,
                            "(VInt " + value.text + ")")
                            : value.sort == Sort.BOOL
                            ? "(VBool " + value.text + ")"
                            : value.sort == Sort.REF
                            ? "(VRef " + value.text + ")"
                            : value.sort == Sort.STRING
                            ? stringValue
                            : value.sort == Sort.FLOAT32
                            ? "(VFloat " + value.text + ")"
                            : value.sort == Sort.FLOAT64
                            ? "(VDouble " + value.text + ")" : "";
                    if (boxed.isEmpty()) {
                        unsupported("ContainerBox:" + value.sort);
                        return null;
                    }
                    return new ContainerSmtCodec.Term(boxed,
                            ContainerSmtCodec.Sort.VALUE);
                }

                @Override
                public ContainerSmtCodec.Term unbox(
                        ContainerSmtCodec.Term value, String javaType) {
                    if (value == null
                            || value.sort != ContainerSmtCodec.Sort.VALUE) {
                        return value;
                    }
                    String kind = ContainerSmtCodec.valueKind(javaType);
                    if (!kind.isEmpty()) {
                        require("((_ is " + kind + ") "
                                + value.text + ")");
                    }
                    String integralValue =
                            ContainerSmtCodec.unboxIntegral(
                                    value.text, javaType);
                    if (!integralValue.isEmpty()) {
                        return new ContainerSmtCodec.Term(
                                integralValue, ContainerSmtCodec.Sort.INT,
                                JavaPrimitiveSmtSemantics.widthOfJavaType(
                                        javaType));
                    }
                    Sort sort = sortOfJava(javaType);
                    if (sort == Sort.BOOL) {
                        return new ContainerSmtCodec.Term(
                                "(valueBool " + value.text + ")",
                                ContainerSmtCodec.Sort.BOOL);
                    }
                    if (sort == Sort.REF) {
                        return new ContainerSmtCodec.Term(
                                "(valueRef " + value.text + ")",
                                ContainerSmtCodec.Sort.REF);
                    }
                    if (sort == Sort.FLOAT32) {
                        return new ContainerSmtCodec.Term(
                                "(valueFloat " + value.text + ")",
                                ContainerSmtCodec.Sort.FLOAT32);
                    }
                    if (sort == Sort.FLOAT64) {
                        return new ContainerSmtCodec.Term(
                                "(valueDouble " + value.text + ")",
                                ContainerSmtCodec.Sort.FLOAT64);
                    }
                    if (sort == Sort.STRING) {
                        return new ContainerSmtCodec.Term(
                                "(valueString " + value.text + ")",
                                ContainerSmtCodec.Sort.STRING);
                    }
                    return value;
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
                    String accessor = "container_field__"
                            + sha256(identity).substring(0, 16);
                    functionDeclarations.put(accessor,
                            "(declare-fun " + accessor + " (Ref) "
                                    + result.smt + ")");
                    return toContainerTerm(new Term("(" + accessor + " "
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

        private static Sort containerSort(ContainerSmtCodec.Sort sort) {
            return sort == ContainerSmtCodec.Sort.BOOL ? Sort.BOOL
                    : sort == ContainerSmtCodec.Sort.INT ? Sort.INT
                    : sort == ContainerSmtCodec.Sort.FLOAT32 ? Sort.FLOAT32
                    : sort == ContainerSmtCodec.Sort.FLOAT64 ? Sort.FLOAT64
                    : sort == ContainerSmtCodec.Sort.STRING ? Sort.STRING
                    : sort == ContainerSmtCodec.Sort.REF ? Sort.REF
                    : Sort.UNKNOWN;
        }

        private ContainerSmtCodec.Term toContainerTerm(Term value) {
            if (value == null) return null;
            ContainerSmtCodec.Sort sort = value.sort == Sort.BOOL
                    ? ContainerSmtCodec.Sort.BOOL
                    : value.sort == Sort.INT
                    ? ContainerSmtCodec.Sort.INT
                    : value.sort == Sort.FLOAT32
                    ? ContainerSmtCodec.Sort.FLOAT32
                    : value.sort == Sort.FLOAT64
                    ? ContainerSmtCodec.Sort.FLOAT64
                    : value.sort == Sort.STRING
                    ? ContainerSmtCodec.Sort.STRING
                    : value.sort == Sort.REF
                    ? ContainerSmtCodec.Sort.REF
                    : value.sort == Sort.VALUE
                    ? ContainerSmtCodec.Sort.VALUE
                    : value.sort == Sort.INDEXED
                    ? ContainerSmtCodec.Sort.INDEXED
                    : value.sort == Sort.ASSOCIATIVE
                    ? ContainerSmtCodec.Sort.ASSOCIATIVE : null;
            return sort == null ? null
                    : new ContainerSmtCodec.Term(value.text, sort,
                    value.integralWidth);
        }

        private Term fromContainerTerm(
                ContainerSmtCodec.Term value, String origin) {
            if (value == null) return null;
            Sort sort = value.sort == ContainerSmtCodec.Sort.BOOL
                    ? Sort.BOOL
                    : value.sort == ContainerSmtCodec.Sort.INT
                    ? Sort.INT
                    : value.sort == ContainerSmtCodec.Sort.FLOAT32
                    ? Sort.FLOAT32
                    : value.sort == ContainerSmtCodec.Sort.FLOAT64
                    ? Sort.FLOAT64
                    : value.sort == ContainerSmtCodec.Sort.STRING
                    ? Sort.STRING
                    : value.sort == ContainerSmtCodec.Sort.REF
                    ? Sort.REF
                    : value.sort == ContainerSmtCodec.Sort.VALUE
                    ? Sort.VALUE
                    : value.sort == ContainerSmtCodec.Sort.INDEXED
                    ? Sort.INDEXED
                    : value.sort == ContainerSmtCodec.Sort.ASSOCIATIVE
                    ? Sort.ASSOCIATIVE : Sort.UNKNOWN;
            if (sort == Sort.UNKNOWN) {
                unsupported.add(origin + ":CONTAINER_STATE_USED_AS_VALUE");
                return null;
            }
            return new Term(value.text, sort, value.integralWidth);
        }

        private Term symbol(JsonObject expression, String origin) {
            String raw = string(expression, "_exp");
            if ("N".equals(raw)) return new Term("nullRef", Sort.REF);
            if ("V".equals(raw)) return new Term("true", Sort.BOOL);
            if (currentConstraintSymbols != null && !raw.isEmpty()) {
                currentConstraintSymbols.add(raw);
            }
            String javaType = string(expression, "_java_type");
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
                symbolNames = new SymbolNames(raw, sort, width);
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
                if (fixedNonNullPlaceholder(raw, sort)) {
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
                return Term.javaString(name, symbolNames.nullness, raw);
            }
            return new Term(name, symbolNames.sort, symbolNames.width);
        }

        private SymbolNames names(String raw) {
            return names.get(raw);
        }

        /**
         * Declares the recorded read cut this query carries.
         *
         * <p>The positions and the selectors are the recorded session's own
         * variables and cannot collide with a port or symbol term. Adding them
         * can never turn a satisfiable query unsatisfiable: the recorded order
         * is acyclic, so the positions always have an assignment, and the
         * unknown-writer arm of every choice carries no order constraint at
         * all. What they add is the one thing the model could not otherwise
         * report - which writer the solver picked.</p>
         */
        private void bindRecordedReadCut(JsonObject payload) {
            if (!RecordedSessionModel.isQueryPayload(payload)) return;
            for (JsonElement element : array(payload, "positions")) {
                JsonObject position = element.getAsJsonObject();
                String name = string(position, "name");
                int bound = integer(position, "bound", 0);
                if (name.isEmpty() || bound <= 0) continue;
                declarations.put(name, Sort.INT);
                assertions.add("(and (<= 0 " + name + ") (< " + name + " "
                        + bound + "))");
            }
            for (JsonElement element : array(payload, "selectors")) {
                String selector = element.getAsString();
                if (selector.isEmpty()) continue;
                declarations.put(selector, Sort.BOOL);
                // Without the selector in the model, the solve reports a
                // choice nobody can read back.
                additionalModelNames.add(selector);
            }
            // README section 6's event-existence Booleans.  Declared, and
            // deliberately not added to the model read-back: they are facts
            // the recorded session already decided, so a solver assignment
            // for them would be a second answer to a question the run
            // answered.
            for (JsonElement element : array(payload, "existenceSymbols")) {
                String symbol = element.getAsString();
                if (!symbol.isEmpty()) declarations.put(symbol, Sort.BOOL);
            }
            // README READ-1's other half.  The recorded model gates each
            // read's exactly-one choice on that read existing and leaves the
            // Boolean to whoever knows which cases contain the load.  This
            // query is stated over one observed target path, and every read
            // in its slice is a load that path performed, so the answer here
            // is that they exist - asserted by name rather than left free,
            // which would let a model report no chosen arm for a read the
            // run watched.
            for (JsonElement element : array(payload, "readChoices")) {
                if (!element.isJsonObject()) continue;
                String symbol = string(element.getAsJsonObject(),
                        "existenceSymbol");
                if (symbol.isEmpty()) continue;
                declarations.put(symbol, Sort.BOOL);
                assertions.add(symbol);
            }
            for (JsonElement element : array(payload, "assertions")) {
                String term = string(element.getAsJsonObject(), "term");
                if (!term.isEmpty()) assertions.add(term);
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
            String function = string(expression, "_place_holder_func");
            int count = integer(expression, "_count", -1);
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
                // invariant. Track it as path support so it cannot stay a
                // free SMT variable while replay materializes only others.
                currentConstraintSymbols.add(
                        "ENVIRONMENT_PLACEHOLDER:" + identity);
            }
            String name = "environment__" + safeName(identity) + "__"
                    + sha256(identity).substring(0, 10);
            declarations.put(name, Sort.INT);
            JavaPrimitiveSmtSemantics.IntegralDomain longDomain =
                    JavaPrimitiveSmtSemantics.domainOfJavaType("J");
            assertions.add("(and (<= " + longDomain.lower + " " + name
                    + ") (<= " + name + " " + longDomain.upper + "))");
            return new Term(name, Sort.INT, IntegralWidth.JAVA_LONG);
        }

        private Term constant(JsonObject expression, Sort expected,
                              String origin) {
            String raw = string(expression, "_exp");
            String payload = constantPayload(raw);
            Sort sort = sortOfJava(string(expression, "_java_type"));
            if (expected == Sort.BOOL && (sort == Sort.INT
                    || sort == Sort.BOOL)) {
                return new Term("0".equals(payload) ? "false" : "true",
                        Sort.BOOL);
            }
            if (expected == Sort.REF && ("0".equals(payload)
                    || "N".equals(raw))) {
                return new Term("nullRef", Sort.REF);
            }
            if (sort == Sort.BOOL) {
                return new Term("0".equals(payload) ? "false" : "true",
                        Sort.BOOL);
            }
            if (sort == Sort.INT) {
                String literal = SmtModelValueCodec.integerLiteral(payload);
                if (literal == null) {
                    unsupported.add(origin + ":INVALID_INTEGER_LITERAL:"
                            + firstNonBlank(raw, "MISSING"));
                    return null;
                }
                return new Term(literal, Sort.INT,
                        JavaPrimitiveSmtSemantics.widthOfJavaType(
                                string(expression, "_java_type")));
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
                return new Term(literal, sort);
            }
            if (sort == Sort.STRING) {
                return Term.nonNullString(quote(payload));
            }
            if ("N".equals(raw)) return new Term("nullRef", Sort.REF);
            unsupported.add(origin + ":UNSUPPORTED_CONSTANT_TYPE:"
                    + firstNonBlank(string(expression, "_java_type"),
                    "MISSING"));
            return null;
        }

        /**
         * Lowers only casts whose value relation is the identity in the
         * current mathematical primitive model.  In particular, an expected
         * sort must never be used to redeclare the source symbol: doing so
         * turns a Java conversion into an unrelated free value.
         */
        private Term typeCast(JsonObject expression, String origin) {
            JsonElement sourceExpression = expression.get("_exp");
            Term source = term(sourceExpression, null, origin + ":castSource");
            String sourceType = JavaPrimitiveSmtSemantics
                    .primitiveDescriptor(
                    firstNonBlank(string(expression, "sourceJavaType"),
                            expressionJavaType(sourceExpression)));
            String targetType = JavaPrimitiveSmtSemantics
                    .primitiveDescriptor(firstNonBlank(
                            string(expression, "targetJavaType"),
                            string(expression, "_java_type")));
            Sort sourceSort = castSort(sourceType);
            Sort targetSort = castSort(targetType);
            boolean primitivePair = JavaPrimitiveSmtSemantics
                    .primitiveNumericDescriptor(sourceType)
                    && JavaPrimitiveSmtSemantics
                    .primitiveNumericDescriptor(targetType);
            if (source != null && primitivePair
                    && source.sort == sourceSort) {
                String conversion = JavaPrimitiveSmtSemantics.primitiveCast(
                        source.text, sourceType, targetType);
                if (conversion != null) {
                    return new Term(conversion, targetSort,
                            JavaPrimitiveSmtSemantics.widthOfJavaType(
                                    targetType));
                }
            } else if (source != null && primitivePair) {
                unsupported.add(origin + ":JAVA_CAST_SOURCE_SORT_CONFLICT:"
                        + firstNonBlank(sourceType, "UNKNOWN") + ":"
                        + source.sort + "!=" + sourceSort);
                return null;
            }
            unsupported.add(origin + ":UNSUPPORTED_JAVA_CAST:"
                    + firstNonBlank(sourceType, "UNKNOWN") + "->"
                    + firstNonBlank(targetType, "UNKNOWN"));
            return null;
        }

        private Term binary(JsonObject expression, String origin) {
            recordFieldAlias(expression);
            String operator = JavaPrimitiveSmtSemantics.canonicalVmOperator(
                    string(expression, "_op"));
            JsonElement leftExpression = expression.get("_left");
            if (leftExpression == null || leftExpression.isJsonNull()) {
                Term operand = term(expression.get("_right"), null,
                        origin + ":operand");
                if ("-".equals(operator) && operand != null
                        && numeric(operand.sort)) {
                    if (operand.sort.floating()) {
                        return new Term(JavaPrimitiveSmtSemantics
                                .floatingNegate(operand.text), operand.sort);
                    }
                    if (operand.integralWidth != IntegralWidth.NONE) {
                        return new Term(JavaPrimitiveSmtSemantics.wrap(
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
                    return new Term(JavaPrimitiveSmtSemantics.complement(
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
                right = new Term("nullRef", Sort.REF);
            } else if (left.sort != right.sort && left.isZero()
                    && right.sort == Sort.REF) {
                left = new Term("nullRef", Sort.REF);
            }
            if ("--".equals(operator)) {
                if (left.sort == Sort.INT && right.sort == Sort.INT
                        && left.integralWidth == IntegralWidth.JAVA_LONG
                        && right.integralWidth == IntegralWidth.JAVA_LONG) {
                    return new Term(JavaPrimitiveSmtSemantics
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
                    return new Term(JavaPrimitiveSmtSemantics
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
                                right.text, symbol.stringNullnessText);
                        if (materialization.isEmpty()) {
                            unsupported.add(origin
                                    + ":STRING_MATERIALIZATION_NULLNESS");
                            return null;
                        }
                        return new Term(materialization, Sort.BOOL);
                    }
                    if (!left.stringReferenceKey.isEmpty()
                            && left.stringReferenceKey.equals(
                            right.stringReferenceKey)) {
                        return new Term("==".equals(operator)
                                ? "true" : "false", Sort.BOOL);
                    }
                    // A BinaryExpression over Java Strings comes from JVM
                    // reference comparison.  SMT string equality is content
                    // equality and would therefore be unsound here.  Content
                    // equality is lowered separately from OpStrExpression.
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
                    return new Term(JavaPrimitiveSmtSemantics
                            .floatingComparison(operator, left.text,
                                    right.text), Sort.BOOL);
                }
                String equals = "(= " + left.text + " " + right.text + ")";
                return new Term("!=".equals(operator)
                        ? "(not " + equals + ")" : equals, Sort.BOOL);
            }
            if ("&&".equals(operator) || "||".equals(operator)) {
                if (left.sort != Sort.BOOL || right.sort != Sort.BOOL) {
                    unsupported.add(origin + ":NON_BOOLEAN_LOGIC");
                    return null;
                }
                return new Term("(" + ("&&".equals(operator) ? "and" : "or")
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
                    return new Term(JavaPrimitiveSmtSemantics
                            .floatingComparison(operator, left.text,
                                    right.text), Sort.BOOL);
                }
                return new Term("(" + comparison + " " + left.text + " "
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
                return new Term(JavaPrimitiveSmtSemantics.bitwise(operator,
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
                return new Term(JavaPrimitiveSmtSemantics.shift(operator,
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
                    unsupported.add(origin + (result.floating()
                            ? ":JAVA_FLOATING_REMAINDER_UNMODELED"
                            : ":JAVA_INTEGRAL_REMAINDER_UNMODELED"));
                    return null;
                }
                if (result.floating()) {
                    String arithmetic = JavaPrimitiveSmtSemantics
                            .floatingArithmetic(operator, left.text,
                                    right.text);
                    if (arithmetic != null) {
                        return new Term(arithmetic, result);
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
                return new Term(JavaPrimitiveSmtSemantics.wrap(
                        arithmeticExpression, resultWidth), Sort.INT,
                        resultWidth);
            }
            unsupported.add(origin + ":BINARY_OPERATOR:" + operator);
            return null;
        }

        private void recordFieldAlias(JsonObject expression) {
            if (!ContainerSmtCodec.handlesFieldBinding(expression)) return;
            JsonElement left = expression.get("_left");
            JsonObject field = ContainerSmtCodec.handlesField(left)
                    ? left.getAsJsonObject()
                    : expression.getAsJsonObject("_right");
            JsonObject symbol = ContainerSmtCodec.handlesField(left)
                    ? expression.getAsJsonObject("_right")
                    : left.getAsJsonObject();
            String raw = string(symbol, "_exp");
            if (raw.isEmpty() || "N".equals(raw) || "V".equals(raw)) {
                return;
            }
            fieldSymbols.computeIfAbsent(CanonicalJson.render(field),
                    ignored -> new LinkedHashSet<>()).add(raw);
        }

        private String materializableFieldRepresentative(
                String raw, List<JsonObject> actions,
                JsonObject activation) {
            String selected = null;
            for (Set<String> aliases : fieldSymbols.values()) {
                if (!aliases.contains(raw)) continue;
                for (String alias : aliases) {
                    SymbolNames aliasNames = names(alias);
                    ActionMatch action = aliasNames == null ? null
                            : materializationResolution(alias, actions,
                            aliasNames.sort);
                    ConfiguredSourceMatch source = aliasNames == null ? null
                            : configuredSourceResolution(alias, activation,
                            aliasNames.sort);
                    if (aliasNames == null
                            || (action == null) == (source == null)) {
                        continue;
                    }
                    // Two distinct writable roots bound to the same field
                    // need coordinated replay writes. The compact context
                    // does not prove which one owns that write, so refuse
                    // instead of selecting one by iteration order.
                    if (selected != null && !selected.equals(alias)) {
                        return null;
                    }
                    selected = alias;
                }
            }
            return selected;
        }

        private void bindSparseContainerBoundaries() {
            for (SparseContainerBoundary boundary
                    : containerBoundaries.boundaries.values()) {
                if (boundary.term == null) {
                    containerBoundaries.gaps.add(boundary.identity()
                            + ":MISSING_ENCODED_READ");
                    continue;
                }
                String identity = boundary.identity() + "\u0000"
                        + boundary.term.text;
                boundary.modelName = "container_boundary__"
                        + sha256(identity).substring(0, 16);
                functionDeclarations.put(boundary.modelName,
                        "(define-fun " + boundary.modelName + " () "
                                + boundary.term.sort.smt + " "
                                + boundary.term.text + ")");
                additionalModelNames.add(boundary.modelName);
                if (boundary.term.sort == Sort.REF
                        && boundary.nullCompared) {
                    boundary.nullModelName = boundary.modelName
                            + "__is_null";
                    functionDeclarations.put(boundary.nullModelName,
                            "(define-fun " + boundary.nullModelName
                                    + " () Bool (= " + boundary.term.text
                                    + " nullRef))");
                    additionalModelNames.add(boundary.nullModelName);
                }
                JavaPrimitiveSmtSemantics.IntegralDomain domain =
                        JavaPrimitiveSmtSemantics.domainOfJavaType(
                                boundary.javaType);
                if (boundary.term.sort == Sort.INT && domain != null) {
                    assertions.add("(and (<= " + domain.lower + " "
                            + boundary.term.text + ") (<= "
                            + boundary.term.text + " " + domain.upper
                            + "))");
                }
                containerBoundaries.models.add(boundary);
            }
        }

        private ReferenceDomains bindReferenceDomains(
                Set<String> frontier, List<JsonObject> actions,
                Set<String> nullableSymbols) {
            ReferenceDomains domains = new ReferenceDomains();
            Map<String, List<JsonObject>> actionsByDomain =
                    referenceActionsByDomain(actions);
            Map<Long, JsonObject> observedSources = new java.util.TreeMap<>();
            for (List<JsonObject> candidates : actionsByDomain.values()) {
                for (JsonObject candidate : candidates) {
                    long identity = longInteger(candidate,
                            "valueObjectId", 0L);
                    JsonObject previous = observedSources.get(identity);
                    if (identity > 0L && (previous == null
                            || string(candidate, "symbol").compareTo(
                            string(previous, "symbol")) < 0)) {
                        observedSources.put(identity, candidate);
                    }
                }
            }
            List<String> observedTerms = new ArrayList<>();
            for (Map.Entry<Long, JsonObject> entry
                    : observedSources.entrySet()) {
                Long identity = entry.getKey();
                String identityName = observedReferenceName(identity);
                declarations.put(identityName, Sort.REF);
                assertions.add("(not (= " + identityName
                        + " nullRef))");
                additionalModelNames.add(identityName);
                domains.addObserved(identityName,
                        string(entry.getValue(), "symbol"));
                observedTerms.add(identityName);
            }
            if (observedTerms.size() > 1) {
                assertions.add("(distinct "
                        + String.join(" ", observedTerms) + ")");
            }
            for (String raw : frontier) {
                SymbolNames symbol = names(raw);
                if (symbol == null || symbol.sort != Sort.REF) continue;
                ActionMatch target = materializationResolution(raw, actions,
                        Sort.REF);
                if (target == null) continue;
                String domainKey = referenceDomainKey(target.action);
                List<JsonObject> candidates = actionsByDomain.get(domainKey);
                if (candidates == null || candidates.isEmpty()) continue;

                Map<Long, JsonObject> sourceByIdentity =
                        new LinkedHashMap<>();
                for (JsonObject candidate : candidates) {
                    long identity = longInteger(candidate,
                            "valueObjectId", 0L);
                    JsonObject previous = sourceByIdentity.get(identity);
                    if (identity > 0L && (previous == null
                            || string(candidate, "symbol").compareTo(
                            string(previous, "symbol")) < 0)) {
                        sourceByIdentity.put(identity, candidate);
                    }
                }
                if (sourceByIdentity.isEmpty()) continue;

                List<String> domainTerms = new ArrayList<>();
                for (Map.Entry<Long, JsonObject> entry
                        : sourceByIdentity.entrySet()) {
                    String identityName = observedReferenceName(
                            entry.getKey());
                    String selector = "select_ref__"
                            + sha256(raw + "\u0000" + identityName)
                            .substring(0, 16);
                    functionDeclarations.put(selector,
                            "(define-fun " + selector + " () Bool (= "
                                    + symbol.solver + " " + identityName
                                    + "))");
                    additionalModelNames.add(selector);
                    domains.add(raw, entry.getKey(),
                            string(entry.getValue(), "symbol"), selector,
                            longInteger(target.action,
                                    "valueObjectId", 0L));
                    domainTerms.add("(= " + symbol.solver + " "
                            + identityName + ")");
                }
                if (nullableSymbols.contains(raw)) {
                    domainTerms.add("(= " + symbol.solver + " nullRef)");
                }
                assertions.add(domainTerms.size() == 1
                        ? domainTerms.get(0)
                        : "(or " + String.join(" ", domainTerms) + ")");
            }
            return domains;
        }

        private static String observedReferenceName(long objectId) {
            return "observed_ref__"
                    + sha256(Long.toString(objectId)).substring(0, 16);
        }

        /**
         * Lowers the Java reference-null view of a String without confusing
         * it with the String's SMT character-content view.  Constants and
         * derived String values carry the exact literal {@code false}; a
         * symbolic input carries its companion nullness Bool.
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
            if (string == null || string.stringNullnessText.isEmpty()) {
                return null;
            }
            String isNull = string.stringNullnessText;
            return new Term("!=".equals(operator)
                    ? "(not " + isNull + ")" : isNull, Sort.BOOL);
        }

        private Term floatingPromotion(Term term, Sort target,
                                       String origin) {
            FloatingKind targetKind = floatingKind(target);
            if (term.sort == target) return term;
            if (term.sort.floating()) {
                String converted = JavaPrimitiveSmtSemantics
                        .floatingConversion(term.text,
                                floatingKind(term.sort), targetKind);
                if (converted != null) return new Term(converted, target);
            } else if (term.sort == Sort.INT
                    && term.integralWidth != IntegralWidth.NONE) {
                String converted = JavaPrimitiveSmtSemantics
                        .integralToFloating(term.text, targetKind);
                if (converted != null) return new Term(converted, target);
            }
            unsupported.add(origin + ":UNSUPPORTED_JAVA_NUMERIC_PROMOTION:"
                    + term.sort + "->" + target);
            return null;
        }

        private Term stringOperation(JsonObject expression, String origin) {
            String operation = string(expression, "_name");
            JsonArray parameters = array(expression, "_param_list");
            boolean negated = bool(expression, "_is_not", false);
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
                Term length = new Term("(str.len "
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
                    return Term.nonNullString(strings.get(0).text);
                }
                StringBuilder result = new StringBuilder("(str.++");
                for (Term value : strings) {
                    result.append(' ').append(value.text);
                }
                return Term.nonNullString(result.append(')').toString());
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
                if (argument.stringNullnessText.isEmpty()) {
                    unsupported.add(origin
                            + ":STRING_EQUALS_NULLABILITY_UNKNOWN:1");
                    return null;
                }
                String contentEquals = "(= " + receiver.text + " "
                        + argument.text + ")";
                predicate = "false".equals(argument.stringNullnessText)
                        ? contentEquals : "(and (not "
                        + argument.stringNullnessText + ") "
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
                // would silently coerce a malformed numeric operand into a
                // string and make an inexact lowering look well-sorted.
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
         * Evaluation of an instance String operation proves its receiver
         * (and each Java-required String argument) non-null.  Keeping that
         * proof separate from the content predicate prevents a null model
         * from satisfying, for example, {@code str.contains}.
         */
        private boolean requireNonNullString(Term value, String origin,
                                             String operation, int index) {
            if (value.stringNullnessText.isEmpty()) {
                unsupported.add(origin + ":STRING_"
                        + operation.toUpperCase(java.util.Locale.ROOT)
                        + "_NULLABILITY_UNKNOWN:" + index);
                return false;
            }
            if (!"false".equals(value.stringNullnessText)) {
                assertions.add("(not " + value.stringNullnessText + ")");
            }
            return true;
        }

        private Term booleanStringResult(String predicate,
                                         boolean negated) {
            return new Term(negated ? "(not " + predicate + ")"
                    : predicate, Sort.BOOL);
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
            String method = firstNonBlank(string(expression, "_name"),
                    "unknown_method");
            // splitElement and parseInt carry the same structural round-trip
            // semantics the composition encoder proves; this mirrors
            // ConcolicSmtComposer.parseIntTerm / splitElementTerm so the two
            // encoders agree on these java.lang methods.  Every other method
            // stays fail-closed as METHOD_SEMANTICS_MISSING.
            if (isJavaParseInt(method)) {
                return parseIntTerm(expression, origin);
            }
            if (isJavaSplitElement(method)) {
                return splitElementTerm(expression, origin);
            }
            unsupported.add(origin + ":METHOD_SEMANTICS_MISSING:" + method);
            return null;
        }

        /**
         * Mirror of {@link ConcolicSmtComposer}'s {@code parseIntTerm}.
         * Recognizes {@code parseInt(splitElement(concat(toString(i), delim,
         * suffix...), delim, [limit], 0)[, 10]) == i} and returns {@code i}.
         * A free parse/split UF would permit models Java cannot execute, so a
         * structural proof is required; anything else is a codec gap.
         */
        private Term parseIntTerm(JsonObject expression, String origin) {
            JsonArray params = array(expression, "_param_list");
            if (params.size() != 1 && params.size() != 2) {
                return codecGap("java/lang/Integer.parseInt", "ARITY", origin);
            }
            if (params.size() == 2) {
                Integer radix = exactIntLiteral(params.get(1));
                if (radix == null || radix != 10) {
                    return codecGap("java/lang/Integer.parseInt",
                            "RADIX_NOT_LITERAL_10", origin);
                }
            }
            SplitPrefix match = exactSplitPrefix(params.get(0));
            if (!match.complete()) {
                return codecGap("java/lang/Integer.parseInt",
                        "ROUNDTRIP_NOT_PROVED_" + match.gap, origin);
            }
            Term integer = term(match.integerExpression, Sort.INT,
                    origin + ":parseInt");
            if (integer == null || integer.sort != Sort.INT) {
                return codecGap("java/lang/Integer.parseInt",
                        "ROUNDTRIP_SOURCE_NOT_INT", origin);
            }
            assertJavaIntRange(integer);
            return integer;
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
            unsupported.add(origin + ":MODEL_SEMANTICS_MISSING:" + operation
                    + ":" + gap);
            return null;
        }

        /**
         * Mirror of {@link ConcolicSmtComposer}'s {@code exactSplitPrefix}.
         * The composer first chases cross-region String equality edges before
         * matching; the path-flip solver works inside a single region and has
         * no such edge index, so the split receiver must already be a
         * syntactic {@code concat(toString(int), delim, suffix...)}.
         */
        private SplitPrefix exactSplitPrefix(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) {
                return SplitPrefix.gap("NOT_METHOD_EXPRESSION");
            }
            JsonObject split = expression.getAsJsonObject();
            if (!"MethodExpression".equals(string(split, "_type"))
                    || !isJavaSplitElement(string(split, "_name"))) {
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
            String delimiter = exactStringLiteral(params.get(1));
            String delimiterGap = decimalDelimiterGap(delimiter);
            if (!delimiterGap.isEmpty()) return SplitPrefix.gap(delimiterGap);
            if (params.size() == 4) {
                Integer limit = exactIntLiteral(params.get(2));
                // Java split(..., 1) returns the entire receiver and therefore
                // does not preserve the decimal prefix as element zero.  Zero,
                // negative limits, and positive limits greater than one do.
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
            // symbolic or non-empty prefixes remain proof gaps.
            List<JsonElement> parts = new ArrayList<>();
            for (JsonElement part : flattened) {
                if (!"".equals(exactStringLiteral(part))) parts.add(part);
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
            if (!"OpStrExpression".equals(string(toString, "_type"))
                    || !"toString".equals(string(toString, "_name"))
                    || bool(toString, "_is_not", false)
                    || toStringParams.size() != 1
                    || !isPrimitiveIntExpression(toStringParams.get(0))) {
                return SplitPrefix.gap("PREFIX_NOT_PRIMITIVE_INT_TO_STRING");
            }
            String concatenatedDelimiter = exactStringLiteral(parts.get(1));
            if (concatenatedDelimiter == null
                    || !delimiter.equals(concatenatedDelimiter)) {
                return SplitPrefix.gap("SPLIT_CONCAT_DELIMITER_MISMATCH");
            }
            for (int indexOfSuffix = 2; indexOfSuffix < parts.size();
                 indexOfSuffix++) {
                if (!provablyStringValued(parts.get(indexOfSuffix))) {
                    return SplitPrefix.gap("SUFFIX_NOT_STRING_VALUED");
                }
            }
            return SplitPrefix.complete(toStringParams.get(0));
        }

        private boolean flattenConcat(JsonElement expression,
                                      List<JsonElement> result) {
            if (expression == null || !expression.isJsonObject()) {
                return false;
            }
            JsonObject object = expression.getAsJsonObject();
            if (!"OpStrExpression".equals(string(object, "_type"))
                    || !"concat".equals(string(object, "_name"))
                    || bool(object, "_is_not", false)) {
                return false;
            }
            JsonArray params = array(object, "_param_list");
            if (params.size() == 0) return false;
            for (JsonElement parameter : params) {
                if (parameter != null && parameter.isJsonObject()
                        && "OpStrExpression".equals(string(
                        parameter.getAsJsonObject(), "_type"))
                        && "concat".equals(string(
                        parameter.getAsJsonObject(), "_name"))) {
                    if (!flattenConcat(parameter, result)) return false;
                } else {
                    result.add(parameter);
                }
            }
            return true;
        }

        private boolean provablyStringValued(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return false;
            JsonObject object = expression.getAsJsonObject();
            String type = string(object, "_type");
            if ("ConStringSymbolExp".equals(type)) return true;
            if ("SymbolExpression".equals(type)
                    || "ConSymbolExp".equals(type)
                    || "ConstExpr".equals(type)) {
                return sortOfJava(string(object, "_java_type")) == Sort.STRING;
            }
            if (!"OpStrExpression".equals(type)
                    || bool(object, "_is_not", false)) return false;
            String operation = string(object, "_name");
            if ("toString".equals(operation)) {
                JsonArray params = array(object, "_param_list");
                return params.size() == 1
                        && isPrimitiveIntExpression(params.get(0));
            }
            if (!"concat".equals(operation)) return false;
            JsonArray params = array(object, "_param_list");
            if (params.size() == 0) return false;
            for (JsonElement parameter : params) {
                if (!provablyStringValued(parameter)) return false;
            }
            return true;
        }

        private boolean isPrimitiveIntExpression(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return false;
            String javaType = string(expression.getAsJsonObject(),
                    "_java_type");
            return "I".equals(javaType) || "int".equals(javaType);
        }

        private Integer exactIntLiteral(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return null;
            JsonObject object = expression.getAsJsonObject();
            String type = string(object, "_type");
            if (!("ConstExpr".equals(type) || "ConSymbolExp".equals(type))) {
                return null;
            }
            String javaType = string(object, "_java_type");
            if (!("I".equals(javaType) || "int".equals(javaType))) {
                return null;
            }
            String value = constantPayload(string(object, "_exp"));
            if (!value.matches("-?[0-9]+")) return null;
            try {
                return Integer.valueOf(value);
            } catch (NumberFormatException ignored) {
                return null;
            }
        }

        private String exactStringLiteral(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return null;
            JsonObject object = expression.getAsJsonObject();
            String type = string(object, "_type");
            if (!("ConStringSymbolExp".equals(type)
                    || "ConstExpr".equals(type)
                    || "ConSymbolExp".equals(type))) return null;
            if (sortOfJava(string(object, "_java_type")) != Sort.STRING) {
                return null;
            }
            return constantPayload(string(object, "_exp"));
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
            return Term.nonNullString("(java_int_to_string "
                    + integer.text + ")");
        }

        private void assertJavaIntRange(Term integer) {
            if (!javaIntRangeAssertions.add(integer.text)) return;
            assertions.add("(and (<= (- 2147483648) " + integer.text
                    + ") (<= " + integer.text + " 2147483647))");
        }

        private String finish() {
            StringBuilder result = new StringBuilder();
            result.append("(set-option :produce-models true)\n");
            // Z3's default arithmetic engine can spend minutes branching on
            // exact Java mod/div identities introduced by constant masks.
            // Solver 2 decides the same bounded integer formulas directly.
            result.append("(set-option :smt.arith.solver 2)\n");
            result.append("(set-logic ALL)\n");
            result.append("(declare-sort Ref 0)\n");
            result.append("(declare-const nullRef Ref)\n");
            result.append(ContainerSmtCodec.valueDatatypeDeclaration())
                    .append('\n');
            for (String declaration : ContainerSmtCodec.preamble()) {
                result.append(declaration).append('\n');
            }
            result.append(JavaPrimitiveSmtSemantics.INT_WRAP_DEFINITION)
                    .append('\n');
            result.append(JavaPrimitiveSmtSemantics.LONG_WRAP_DEFINITION)
                    .append('\n');
            if (usesJavaIntString) {
                // SMT-LIB's str.from_int is defined only for non-negative
                // integers; Java's decimal Integer.toString additionally emits
                // a leading '-'.  Mirrors ConcolicSmtComposer's preamble so the
                // split/parseInt round trip is ordinary string semantics rather
                // than an unconstrained UF.
                result.append("(define-fun java_int_to_string ((i Int)) "
                        + "String (ite (< i 0) (str.++ \"-\" "
                        + "(str.from_int (- i))) (str.from_int i)))\n");
            }
            for (Map.Entry<String, Sort> declaration
                    : declarations.entrySet()) {
                result.append("(declare-const ").append(declaration.getKey())
                        .append(' ').append(declaration.getValue().smt)
                        .append(")\n");
            }
            for (String declaration : functionDeclarations.values()) {
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
            for (int index = 0; index < assertions.size(); index++) {
                result.append("(assert (! ").append(assertions.get(index))
                        .append(" :named pc_").append(index).append("))\n");
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

    private enum Sort {
        BOOL("Bool"), INT("Int"),
        FLOAT32("(_ FloatingPoint 8 24)"),
        FLOAT64("(_ FloatingPoint 11 53)"), STRING("String"),
        REF("Ref"), VALUE("Value"),
        INDEXED("IndexedState"), ASSOCIATIVE("AssocState"),
        UNKNOWN("");

        private final String smt;

        Sort(String smt) {
            this.smt = smt;
        }

        private boolean containerState() {
            return this == INDEXED || this == ASSOCIATIVE;
        }

        private boolean floating() {
            return this == FLOAT32 || this == FLOAT64;
        }
    }

    private static final class Term {
        private final String text;
        private final Sort sort;
        private final IntegralWidth integralWidth;
        private final String stringNullnessText;
        private final String stringReferenceKey;

        private Term(String text, Sort sort) {
            this(text, sort, IntegralWidth.NONE, "", "");
        }

        private Term(String text, Sort sort,
                     IntegralWidth integralWidth) {
            this(text, sort, integralWidth, "", "");
        }

        private Term(String text, Sort sort,
                     IntegralWidth integralWidth,
                     String stringNullnessText,
                     String stringReferenceKey) {
            this.text = text;
            this.sort = sort;
            this.integralWidth = sort == Sort.INT && integralWidth != null
                    ? integralWidth : IntegralWidth.NONE;
            this.stringNullnessText = stringNullnessText == null
                    ? "" : stringNullnessText;
            this.stringReferenceKey = stringReferenceKey == null
                    ? "" : stringReferenceKey;
        }

        private static Term javaString(String content,
                                       String nullness,
                                       String referenceKey) {
            return new Term(content, Sort.STRING, IntegralWidth.NONE,
                    nullness, referenceKey);
        }

        private static Term nonNullString(String content) {
            return new Term(content, Sort.STRING, IntegralWidth.NONE,
                    "false", "");
        }

        private boolean isZero() {
            return "0".equals(text);
        }

        private boolean isNullReference() {
            return sort == Sort.REF && "nullRef".equals(text);
        }
    }

    private static ModelProjection modelAssignments(
            Encoder encoder, Map<String, String> values,
            List<JsonObject> actions, JsonObject activation,
            Set<String> projectedSymbols,
            ReferenceDomains referenceDomains) {
        JsonArray result = new JsonArray();
        Set<String> unresolved = new LinkedHashSet<>(projectedSymbols);
        for (String raw : encoder.controlledSymbols) {
            if (!projectedSymbols.contains(raw)) continue;
            SymbolNames names = encoder.names(raw);
            String solverName = names.solver;
            Sort sort = names.sort;
            String modelName = sort.floating()
                    ? names.floatingBits : solverName;
            String value = values.get(modelName);
            String nanValue = sort.floating()
                    ? values.get(names.floatingNaN) : "";
            String nullValue = sort == Sort.STRING || sort == Sort.REF
                    ? values.get(names.nullness) : "";
            boolean reference = sort == Sort.REF;
            if ((!reference && value == null) || sort.containerState()
                    || sort.floating() && !("true".equals(nanValue)
                    || "false".equals(nanValue))
                    || sort == Sort.STRING
                    && !("true".equals(nullValue)
                    || "false".equals(nullValue))
                    || reference
                    && !("true".equals(nullValue)
                    || "false".equals(nullValue))) continue;
            ActionMatch match = materializationResolution(raw, actions, sort);
            ConfiguredSourceMatch source = configuredSourceResolution(
                    raw, activation, sort);
            if ((match == null) == (source == null)) continue;
            ReferenceChoice referenceChoice = reference
                    && "false".equals(nullValue)
                    ? referenceDomains.selected(raw, values) : null;
            if (reference && "false".equals(nullValue)
                    && referenceChoice == null) {
                continue;
            }
            if (reference && referenceChoice != null
                    && referenceChoice.sourceIdentity
                    == referenceChoice.targetIdentity) {
                unresolved.remove(raw);
                continue;
            }
            JsonObject assignment = new JsonObject();
            assignment.addProperty("engineSymbol", raw);
            if (sort == Sort.STRING) {
                assignment.addProperty("modelIsNull",
                        "true".equals(nullValue));
            } else if (reference) {
                assignment.addProperty("modelIsNull", true);
            }
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
                assignment.addProperty("inputSymbol", string(match.action,
                        "symbol"));
            }
            if (reference) {
                if ("true".equals(nullValue)) {
                    assignment.addProperty("valueType", "NULL");
                    assignment.addProperty("value", "null");
                } else {
                    assignment.addProperty("valueType", "REFERENCE_ALIAS");
                    assignment.addProperty("referenceSourceInputSymbol",
                            referenceChoice.sourceInputSymbol);
                }
            } else if (sort.floating()) {
                String descriptor = sort == Sort.FLOAT32 ? "F" : "D";
                boolean isNaN = "true".equals(nanValue);
                String decoded = isNaN ? "NaN" : SmtModelValueCodec
                        .floatingPointBitsToJavaLiteral(value, descriptor);
                if (decoded == null) continue;
                assignment.addProperty("valueType", "REAL");
                assignment.addProperty("value", decoded);
            } else if (sort == Sort.STRING
                    && "true".equals(nullValue)) {
                assignment.addProperty("valueType", "NULL");
                assignment.addProperty("value", "null");
            } else {
                assignment.addProperty("valueType", sort.name());
                assignment.addProperty("value",
                        SmtModelValueCodec.normalizeScalar(value));
            }
            if (match != null) {
                List<String> actionPath = stringList(array(match.action,
                        "fieldPath"));
                List<String> replayPath = !match.path.isEmpty()
                        ? match.path : actionPath;
                if (!replayPath.isEmpty()) {
                    assignment.add("materializationPath",
                            strings(replayPath));
                }
            }
            result.add(assignment);
            unresolved.remove(raw);
        }
        return new ModelProjection(result, unresolved);
    }

    private static ModelProjection sparseContainerAssignments(
            Map<String, String> values,
            SparseContainerBoundaries boundaries,
            ReferenceDomains referenceDomains,
            int targetOccurrence) {
        JsonArray assignments = new JsonArray();
        Set<String> unresolved = new LinkedHashSet<>();
        Map<String, List<SparseContainerBoundary>> referenceGroups =
                new LinkedHashMap<>();
        for (SparseContainerBoundary boundary : boundaries.models) {
            String value = values.get(boundary.modelName);
            if (value == null || boundary.action == null) {
                unresolved.add(boundary.modelName);
                continue;
            }
            if (boundary.term.sort == Sort.REF) {
                if (!boundary.nullModelName.isEmpty()) {
                    String nullness = values.get(boundary.nullModelName);
                    if ("true".equals(nullness)) {
                        assignments.add(containerAssignment(
                                boundary, "NULL", "null",
                                targetOccurrence));
                        continue;
                    }
                    if (!"false".equals(nullness)) {
                        unresolved.add(boundary.modelName);
                        continue;
                    }
                }
                referenceGroups.computeIfAbsent(value,
                        ignored -> new ArrayList<>()).add(boundary);
                continue;
            }
            assignments.add(containerAssignment(boundary,
                    boundary.term.sort.name(),
                    SmtModelValueCodec.normalizeScalar(value),
                    targetOccurrence));
        }
        for (Map.Entry<String, List<SparseContainerBoundary>> entry
                : referenceGroups.entrySet()) {
            List<SparseContainerBoundary> group = entry.getValue();
            group.sort(Comparator.comparing(
                    SparseContainerBoundary::identity));
            String modelValue = entry.getKey();
            String ordinarySource =
                    referenceDomains.sourceForModelValue(modelValue, values);
            if (!ordinarySource.isEmpty()) {
                for (SparseContainerBoundary target : group) {
                    JsonObject assignment = containerAssignment(target,
                            "CONTAINER_REFERENCE_ALIAS", "",
                            targetOccurrence);
                    assignment.addProperty("referenceSourceInputSymbol",
                            ordinarySource);
                    assignments.add(assignment);
                }
                continue;
            }
            if (group.size() < 2) {
                SparseContainerBoundary only = group.get(0);
                if (!only.preferredReferenceSource) {
                    unresolved.add(only.modelName);
                }
                continue;
            }
            SparseContainerBoundary source = group.get(0);
            for (SparseContainerBoundary candidate : group) {
                if (candidate.preferredReferenceSource) {
                    source = candidate;
                    break;
                }
            }
            for (SparseContainerBoundary target : group) {
                if (target == source) continue;
                JsonObject assignment = containerAssignment(target,
                        "CONTAINER_REFERENCE_ALIAS", "",
                        targetOccurrence);
                assignment.addProperty("referenceSourceInputSymbol",
                        string(source.action, "symbol"));
                target.addSourceSelector(
                        assignment.getAsJsonObject("containerTarget"),
                        source);
                assignments.add(assignment);
            }
        }
        return new ModelProjection(assignments, unresolved);
    }

    private static JsonObject containerAssignment(
            SparseContainerBoundary boundary, String valueType,
            String value, int targetOccurrence) {
            JsonObject assignment = new JsonObject();
            assignment.addProperty("modelAssignmentKey",
                    boundary.modelName);
            assignment.addProperty("engineSymbol", boundary.modelName);
            assignment.addProperty("inputSymbol",
                    string(boundary.action, "symbol"));
            assignment.addProperty("valueType", valueType);
            if (!value.isEmpty()) assignment.addProperty("value", value);
            JsonObject target = new JsonObject();
            boundary.addSelector(target, targetOccurrence);
            assignment.add("containerTarget", target);
            return assignment;
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

    private static final class ReplaySupport {
        private final Set<String> writableSymbols;
        private final Set<String> unresolvedSymbols;

        private ReplaySupport(Set<String> writableSymbols,
                              Set<String> unresolvedSymbols) {
            this.writableSymbols = writableSymbols;
            this.unresolvedSymbols = unresolvedSymbols;
        }
    }

    /**
     * Classifies target-prefix support before the real encoder is built.
     *
     * <p>A target path flip is a local replay of one predecessor decision.
     * Exact remote predecessors remain in {@link BranchReplayContract} and
     * are checked by the full-session replay, but they are deliberately not
     * asserted as free variables in the local SMT query.  No such omission is
     * allowed for a predicate that also contains a writable local root: that
     * would require a typed concrete snapshot of the companion value, which
     * the current handoff/read-from evidence does not carry.</p>
     */
    private static final class TargetReplaySupportPlan {
        private final Set<Integer> externalCompanionPredicates;
        private final String gapReason;
        private final Set<String> gapSymbols;

        private TargetReplaySupportPlan(
                Set<Integer> externalCompanionPredicates,
                String gapReason, Set<String> gapSymbols) {
            this.externalCompanionPredicates =
                    externalCompanionPredicates;
            this.gapReason = gapReason;
            this.gapSymbols = gapSymbols;
        }

        private static TargetReplaySupportPlan notTarget() {
            return new TargetReplaySupportPlan(
                    Collections.<Integer>emptySet(), "",
                    Collections.<String>emptySet());
        }

        private static TargetReplaySupportPlan build(
                JsonObject task, JsonObject activation,
                JsonArray predicates, JsonArray context,
                List<JsonObject> actions) {
            SparseContainerBoundaries boundaries =
                    SparseContainerBoundaries.discover(
                            predicates, context, actions);
            Encoder probe = new Encoder(boundaries);
            for (int index = 0; index < context.size(); index++) {
                JsonElement constraint = context.get(index);
                if (!boundaries.isConcreteObservation(constraint)) {
                    probe.addConstraint(constraint,
                            "q_target_support_context_" + index);
                }
            }
            List<Set<String>> symbolsByPredicate = new ArrayList<>();
            for (int index = 0; index < predicates.size(); index++) {
                symbolsByPredicate.add(probe.addConstraint(
                        predicates.get(index),
                        "q_target_support_branch_" + index));
            }

            CompanionSupport companions = CompanionSupport.from(
                    task, actions);
            Set<Integer> external = new LinkedHashSet<>();
            Set<String> ambiguous = new LinkedHashSet<>();
            Set<String> missing = new LinkedHashSet<>();
            Set<String> mixed = new LinkedHashSet<>();
            boolean selectedHasWritableRoot = false;
            int selected = predicates.size() - 1;

            for (int index = 0; index < symbolsByPredicate.size(); index++) {
                ReplaySupport local = classifyReplaySupport(
                        probe, symbolsByPredicate.get(index), actions,
                        activation);
                Set<String> exactCompanion = new LinkedHashSet<>();
                Set<String> predicateMissing = new LinkedHashSet<>();
                Set<String> predicateAmbiguous = new LinkedHashSet<>();
                for (String unresolved : local.unresolvedSymbols) {
                    SymbolNames names = probe.names(unresolved);
                    CompanionResolution resolution = companions.resolve(
                            unresolved, names == null
                                    ? Sort.UNKNOWN : names.sort);
                    if (resolution == CompanionResolution.EXACT) {
                        exactCompanion.add(unresolved);
                    } else if (resolution
                            == CompanionResolution.AMBIGUOUS) {
                        predicateAmbiguous.add(unresolved);
                    } else {
                        predicateMissing.add(unresolved);
                    }
                }
                ambiguous.addAll(predicateAmbiguous);
                missing.addAll(predicateMissing);
                if (!local.writableSymbols.isEmpty()
                        && !exactCompanion.isEmpty()) {
                    mixed.addAll(local.writableSymbols);
                    mixed.addAll(exactCompanion);
                }
                if (index == selected) {
                    selectedHasWritableRoot =
                            !local.writableSymbols.isEmpty();
                }
                if (local.writableSymbols.isEmpty()
                        && !exactCompanion.isEmpty()
                        && predicateMissing.isEmpty()
                        && predicateAmbiguous.isEmpty()) {
                    external.add(index);
                }
            }

            if (!ambiguous.isEmpty()) {
                return new TargetReplaySupportPlan(external,
                        "TARGET_PREFIX_COMPANION_SUPPORT_AMBIGUOUS",
                        ambiguous);
            }
            if (!missing.isEmpty()) {
                return new TargetReplaySupportPlan(external,
                        "TARGET_PREFIX_COMPANION_SUPPORT_MISSING", missing);
            }
            if (!mixed.isEmpty()) {
                return new TargetReplaySupportPlan(external,
                        "TARGET_PREFIX_MIXES_LOCAL_AND_COMPANION_SUPPORT",
                        mixed);
            }
            if (!selectedHasWritableRoot) {
                Set<String> selectedSymbols = new LinkedHashSet<>();
                if (selected >= 0) {
                    selectedSymbols.addAll(symbolsByPredicate.get(selected));
                }
                return new TargetReplaySupportPlan(external,
                        "TARGET_PREFIX_FLIP_HAS_NO_LOCAL_WRITABLE_ROOT",
                        selectedSymbols);
            }
            return new TargetReplaySupportPlan(external, "",
                    Collections.<String>emptySet());
        }

        private boolean isExternalCompanion(int index) {
            return externalCompanionPredicates.contains(index);
        }

        private boolean hasGap() {
            return !gapReason.isEmpty();
        }

        private String reason() {
            return gapReason;
        }

        private Set<String> gapSymbols() {
            return gapSymbols;
        }
    }

    private enum CompanionResolution {
        NONE,
        EXACT,
        AMBIGUOUS
    }

    /** Exact non-local authorities available to one target replay query. */
    private static final class CompanionSupport {
        private final Map<String, Set<String>> rpcAuthorities =
                new LinkedHashMap<>();
        private final List<SharedCompanion> shared = new ArrayList<>();

        private static CompanionSupport from(
                JsonObject task, List<JsonObject> actions) {
            CompanionSupport result = new CompanionSupport();
            for (JsonObject event : VmHandoffEvidence.eventsOf(task)) {
                Set<String> symbols = new LinkedHashSet<>();
                collectEngineSymbols(event.get(
                        VmHandoffEvidence.EXPRESSION), symbols);
                String authority = "RPC\u0000"
                        + string(event, VmHandoffEvidence.PRODUCER_TASK_ID)
                        + "\u0000" + string(event,
                        VmHandoffEvidence.PRODUCER_OCCURRENCE_ID);
                for (String symbol : symbols) {
                    result.rpcAuthorities.computeIfAbsent(symbol,
                            ignored -> new LinkedHashSet<>()).add(authority);
                }
            }
            for (JsonElement element : array(task, "edgeBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                boolean exact = RecordedReadFrom.PROVENANCE_EXACT.equals(
                        string(binding, RecordedReadFrom.EDGE_PROVENANCE));
                if (!exact || !(AutomaticRegionEdge
                        .trustedRuntimeReadFromBinding(binding)
                        || AutomaticRegionEdge
                        .trustedVmRecordedReadFromEvidence(binding))) {
                    continue;
                }
                String port = string(binding, "toInputPort");
                List<JsonObject> matches = new ArrayList<>();
                for (JsonObject action : actions) {
                    if ("CONCRETE".equals(string(action, "mode"))
                            && port.equals(string(action, "symbol"))) {
                        matches.add(action);
                    }
                }
                if (matches.size() != 1) continue;
                String authority = "SHARED\u0000"
                        + string(binding, "fromOccurrenceId") + "\u0000"
                        + string(binding, "fromOutputPort");
                result.shared.add(new SharedCompanion(port,
                        materializationSort(matches.get(0)), authority));
            }
            return result;
        }

        private CompanionResolution resolve(String raw, Sort sort) {
            Set<String> authorities = new LinkedHashSet<>();
            authorities.addAll(rpcAuthorities.getOrDefault(raw,
                    Collections.<String>emptySet()));
            for (SharedCompanion candidate : shared) {
                if ((sort == Sort.UNKNOWN || candidate.sort == sort)
                        && matchesEngineSymbol(raw, candidate.inputPort)) {
                    authorities.add(candidate.authority);
                }
            }
            if (authorities.isEmpty()) return CompanionResolution.NONE;
            return authorities.size() == 1
                    ? CompanionResolution.EXACT
                    : CompanionResolution.AMBIGUOUS;
        }
    }

    private static final class SharedCompanion {
        private final String inputPort;
        private final Sort sort;
        private final String authority;

        private SharedCompanion(String inputPort, Sort sort,
                                String authority) {
            this.inputPort = inputPort;
            this.sort = sort;
            this.authority = authority;
        }
    }

    private static final class SparseContainerBoundaries {
        private final Map<String, SparseContainerBoundary> boundaries =
                new LinkedHashMap<>();
        private final Set<String> gaps = new LinkedHashSet<>();
        private final List<SparseContainerBoundary> models =
                new ArrayList<>();
        private final Map<String, Set<String>> retainedCellsByPort =
                new LinkedHashMap<>();

        private static SparseContainerBoundaries discover(
                JsonArray predicates, JsonArray context,
                List<JsonObject> actions) {
            SparseContainerBoundaries result =
                    new SparseContainerBoundaries();
            String capacityIssue = InitialContainerObservation
                    .failureRelevantCapacityIssue(predicates);
            if (!capacityIssue.isEmpty()) {
                result.gaps.add(capacityIssue);
            }
            result.scan(predicates, true, false);
            result.scan(context, false, false);
            for (SparseContainerBoundary boundary
                    : result.boundaries.values()) {
                List<JsonObject> matches = containerBoundaryActions(
                        boundary.stateSymbol, actions);
                if (matches.size() == 1) {
                    boundary.action = matches.get(0).deepCopy();
                } else {
                    result.gaps.add(boundary.identity()
                            + ":REF_ACTION_MATCHES=" + matches.size());
                }
            }
            return result;
        }

        private void scan(JsonElement element, boolean discover,
                          boolean preferredReferenceSource) {
            if (element == null || element.isJsonNull()) return;
            if (element.isJsonArray()) {
                for (JsonElement child : element.getAsJsonArray()) {
                    scan(child, discover, preferredReferenceSource);
                }
                return;
            }
            if (!element.isJsonObject()) return;
            JsonObject object = element.getAsJsonObject();
            InitialContainerObservation.Read read =
                    InitialContainerObservation.initialRead(object);
            if (read != null) {
                if (!read.concreteSelector()) {
                    if (discover && !read.dynamicAssociativeSelector()) {
                        gaps.add(read.shape + ":"
                            + read.stateSymbol
                            + ":NON_CONCRETE_SELECTOR");
                    }
                } else {
                    String identity = boundaryIdentity(read);
                    SparseContainerBoundary existing =
                            boundaries.get(identity);
                    if (existing == null && discover) {
                        if (retainFailureRelevantCell(read)) {
                            boundaries.put(identity,
                                    new SparseContainerBoundary(read));
                        }
                    } else if (existing != null
                            && !JavaPrimitiveSmtSemantics
                            .javaTypeDescriptor(existing.javaType)
                            .equals(JavaPrimitiveSmtSemantics
                                    .javaTypeDescriptor(read.javaType))) {
                        gaps.add(existing.identity()
                                + ":CONFLICTING_JAVA_TYPES");
                    }
                    existing = boundaries.get(identity);
                    if (existing != null && preferredReferenceSource) {
                        existing.preferredReferenceSource = true;
                    }
                }
            }
            boolean fieldAccess = "FieldAccessExpression".equals(
                    string(object, "_type"));
            for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
                scan(entry.getValue(), discover,
                        fieldAccess && "owner".equals(entry.getKey())
                                || preferredReferenceSource);
            }
            if (discover) markNullComparison(object);
        }

        private boolean retainFailureRelevantCell(
                InitialContainerObservation.Read read) {
            Set<String> retained = retainedCellsByPort.computeIfAbsent(
                    read.inputPort, ignored -> new LinkedHashSet<>());
            String cell = read.shape + "\u0000"
                    + read.selectorIdentity();
            if (retained.contains(cell)) return true;
            if (retained.size() >= LoopBoundPolicy
                    .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY) {
                return false;
            }
            retained.add(cell);
            return true;
        }

        private void markNullComparison(JsonObject expression) {
            if (!"BinaryExpression".equals(string(expression, "_type"))) {
                return;
            }
            markNullComparison(expression.get("_left"),
                    expression.get("_right"));
            markNullComparison(expression.get("_right"),
                    expression.get("_left"));
        }

        private void markNullComparison(JsonElement readElement,
                                        JsonElement otherElement) {
            if (readElement == null || !readElement.isJsonObject()
                    || otherElement == null || !otherElement.isJsonObject()
                    || !"SymbolExpression".equals(string(
                    otherElement.getAsJsonObject(), "_type"))
                    || !"N".equals(string(otherElement.getAsJsonObject(),
                    "_exp"))) {
                return;
            }
            InitialContainerObservation.Read read =
                    InitialContainerObservation.initialRead(
                            readElement.getAsJsonObject());
            if (read == null || !read.concreteSelector()
                    && !read.dynamicAssociativeSelector()) return;
            String identity = boundaryIdentity(read);
            SparseContainerBoundary boundary = boundaries.get(identity);
            if (boundary == null && read.dynamicAssociativeSelector()
                    && retainFailureRelevantCell(read)) {
                boundary = new SparseContainerBoundary(read);
                boundaries.put(identity, boundary);
            }
            if (boundary != null) boundary.nullCompared = true;
        }

        private boolean isConcreteObservation(JsonElement expression) {
            return InitialContainerObservation.isConcreteEquality(
                    expression);
        }

        private void record(JsonObject expression,
                            ContainerSmtCodec.Term encoded) {
            InitialContainerObservation.Read read =
                    InitialContainerObservation.initialRead(expression);
            if (read == null || !read.concreteSelector()
                    && !read.dynamicAssociativeSelector()
                    || encoded == null) {
                return;
            }
            SparseContainerBoundary boundary = boundaries.get(
                    boundaryIdentity(read));
            if (boundary == null) return;
            Sort sort = Encoder.containerSort(encoded.sort);
            if (sort != Sort.INT && sort != Sort.BOOL
                    && sort != Sort.REF) {
                gaps.add(boundary.identity()
                        + ":UNSUPPORTED_READ_SORT=" + sort);
                return;
            }
            Term term = new Term(encoded.text, sort,
                    encoded.integralWidth);
            record(boundary, term);
        }

        private void record(SparseContainerBoundary boundary, Term term) {
            if (boundary.term == null) {
                boundary.term = term;
            } else if (boundary.term.sort != term.sort
                    || !boundary.term.text.equals(term.text)) {
                gaps.add(boundary.identity()
                        + ":INCONSISTENT_ENCODED_READ");
            }
        }

        private SparseContainerBoundary dynamicAssociativeBoundary(
                JsonObject expression) {
            InitialContainerObservation.Read read =
                    InitialContainerObservation.initialRead(expression);
            if (read == null || !read.dynamicAssociativeSelector()) {
                return null;
            }
            SparseContainerBoundary boundary = boundaries.get(
                    boundaryIdentity(read));
            return boundary != null && boundary.nullCompared
                    ? boundary : null;
        }

        private static String boundaryIdentity(
                InitialContainerObservation.Read read) {
            return read.shape + "\u0000" + read.stateSymbol + "\u0000"
                    + read.selectorIdentity();
        }
    }

    private static final class SparseContainerBoundary {
        private final String shape;
        private final String stateSymbol;
        private final int index;
        private final String keyJavaType;
        private final String keyValue;
        private final String selectorIdentity;
        private final String iterationProjection;
        private final String javaType;
        private JsonObject action;
        private Term term;
        private String modelName = "";
        private String nullModelName = "";
        private boolean nullCompared;
        private boolean preferredReferenceSource;

        private SparseContainerBoundary(
                InitialContainerObservation.Read read) {
            this.shape = read.shape;
            this.stateSymbol = read.stateSymbol;
            this.index = read.index == null ? -1 : read.index;
            this.keyJavaType = read.keyJavaType();
            this.keyValue = read.keyValue();
            this.selectorIdentity = read.selectorIdentity();
            this.iterationProjection = read.iterationProjection;
            this.javaType = read.javaType;
        }

        private String identity() {
            return shape + ":" + stateSymbol + "["
                    + selectorIdentity + "]";
        }

        private String selectorIdentity() {
            return selectorIdentity;
        }

        private void addSelector(JsonObject target, int targetOccurrence) {
            target.addProperty("shape", shape);
            if ("ASSOCIATIVE".equals(shape) && nullCompared
                    && targetOccurrence > 0) {
                target.addProperty("selectorKind", "ACCESS_ORDINAL");
                target.addProperty("accessOrdinal", targetOccurrence);
                return;
            }
            if ("INDEXED".equals(shape)) {
                target.addProperty("index", index);
            } else if (!iterationProjection.isEmpty()) {
                target.addProperty("selectorKind", "ITERATION_INDEX");
                target.addProperty("index", index);
                target.addProperty("projection", iterationProjection);
            } else {
                target.addProperty("keyJavaType", keyJavaType);
                target.addProperty("keyValue", keyValue);
            }
        }

        private void addSourceSelector(JsonObject target,
                                       SparseContainerBoundary source) {
            target.addProperty("sourceShape", source.shape);
            if ("INDEXED".equals(source.shape)) {
                target.addProperty("sourceIndex", source.index);
            } else {
                target.addProperty("sourceKeyJavaType",
                        source.keyJavaType);
                target.addProperty("sourceKeyValue", source.keyValue);
            }
        }
    }

    private static final class ReferenceDomains {
        private final Map<String, List<ReferenceChoice>> choices =
                new LinkedHashMap<>();
        private final Map<String, String> observedSources =
                new LinkedHashMap<>();

        private void addObserved(String modelName, String inputSymbol) {
            if (!modelName.isEmpty() && !inputSymbol.isEmpty()) {
                observedSources.put(modelName, inputSymbol);
            }
        }

        private void add(String raw, long sourceIdentity,
                         String sourceInputSymbol, String selector,
                         long targetIdentity) {
            choices.computeIfAbsent(raw,
                    ignored -> new ArrayList<>()).add(
                    new ReferenceChoice(sourceIdentity, sourceInputSymbol,
                            selector, targetIdentity));
        }

        private ReferenceChoice selected(String raw,
                                         Map<String, String> values) {
            for (ReferenceChoice choice : choices.getOrDefault(raw,
                    Collections.<ReferenceChoice>emptyList())) {
                if ("true".equals(values.get(choice.selector))) {
                    return choice;
                }
            }
            return null;
        }

        private String sourceForModelValue(
                String modelValue, Map<String, String> values) {
            String selected = "";
            for (Map.Entry<String, String> source
                    : observedSources.entrySet()) {
                if (!modelValue.equals(values.get(source.getKey()))) {
                    continue;
                }
                if (selected.isEmpty()
                        || source.getValue().compareTo(selected) < 0) {
                    selected = source.getValue();
                }
            }
            return selected;
        }
    }

    private static final class ReferenceChoice {
        private final long sourceIdentity;
        private final String sourceInputSymbol;
        private final String selector;
        private final long targetIdentity;

        private ReferenceChoice(long sourceIdentity,
                                String sourceInputSymbol,
                                String selector,
                                long targetIdentity) {
            this.sourceIdentity = sourceIdentity;
            this.sourceInputSymbol = sourceInputSymbol;
            this.selector = selector;
            this.targetIdentity = targetIdentity;
        }
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
                value -> string(value, "symbol")));
        return declared;
    }

    private static final class PathQuery {
        private final String queryKey;
        private final BranchReplayContract replayContract;
        private final SolverPathContext pathContext;
        /**
         * The recorded guarded reads this query may select among, or the
         * empty object when the session recorded none that reach it.
         */
        private final JsonObject recordedReadCut;

        private PathQuery(String queryKey,
                          BranchReplayContract replayContract,
                          SolverPathContext pathContext,
                          JsonObject recordedReadCut) {
            this.queryKey = queryKey;
            this.replayContract = replayContract;
            this.pathContext = pathContext;
            this.recordedReadCut = recordedReadCut;
        }

        private static PathQuery decode(JsonObject task) throws IOException {
            if (integer(task, "schemaVersion", -1) != 3
                    || !"REGION_PATH_FLIP".equals(string(task, "kind"))) {
                throw new IOException(
                        "canonical path task requires REGION_PATH_FLIP "
                                + "schema 3");
            }
            String queryKey = string(task, "queryKey");
            if (!canonicalQueryKey(queryKey)) {
                throw new IOException(
                        "canonical path task requires SHA-256 queryKey");
            }
            JsonObject readCut = object(task,
                    RecordedSessionModel.QUERY_FIELD);
            if (readCut.size() > 0
                    && !RecordedSessionModel.isQueryPayload(readCut)) {
                throw new IOException(
                        "canonical path task carries an unadmitted recorded "
                                + "read cut");
            }
            try {
                return new PathQuery(queryKey,
                        BranchReplayContract.fromJson(
                        requiredObject(task, "replayContract")),
                        SolverPathContext.fromJson(requiredObject(task,
                                "solverPathContext")), readCut);
            } catch (IllegalArgumentException malformed) {
                throw new IOException("invalid canonical path task: "
                        + malformed.getMessage(), malformed);
            }
        }
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
            String symbol = string(action, "symbol");
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
                String label = symbol + (segments.isEmpty() ? ""
                        : "." + String.join(".", segments));
                if (matchesEngineSymbol(raw, label)
                        && label.length() > bestLength) {
                    best = new ActionMatch(action, segments);
                    bestLength = label.length();
                }
            }
        }
        return best;
    }

    private static ActionMatch materializationResolution(
            String raw, List<JsonObject> actions, Sort expectedSort) {
        return bestAction(raw, actions, expectedSort);
    }

    /**
     * Resolves one VM source root to the exact configured Java field whose
     * concrete value replay may change before minting that same source root.
     * This is deliberately separate from ordinary input actions: turning a
     * configured source into every matching getfield would mint a different
     * symbol at each access and destroy its cross-case identity.
     */
    private static ConfiguredSourceMatch configuredSourceResolution(
            String raw, JsonObject activation, Sort expectedSort) {
        if (raw == null || raw.isEmpty()
                || expectedSort == null || expectedSort == Sort.UNKNOWN
                || expectedSort == Sort.REF || expectedSort == Sort.STRING
                || expectedSort.containerState()) {
            return null;
        }
        ConfiguredSourceMatch selected = null;
        for (JsonElement element : array(activation,
                SymbolicSourceEvidence.TASK_FIELD)) {
            if (!element.isJsonObject()) return null;
            JsonObject declaration = element.getAsJsonObject();
            String sourceId = string(declaration, "sourceId");
            String sourcePhaseId = string(declaration, "sourcePhaseId");
            String fieldSignature = string(declaration, "fieldSignature");
            FieldPathSpec.DeclaredField field =
                    FieldPathSpec.declaredField(fieldSignature);
            if (!SymbolicSourceEvidence.DECLARATION_AUTHORITY.equals(
                    string(declaration, "authority"))
                    || sourceId.isEmpty() || sourcePhaseId.isEmpty()
                    || field == null
                    || sortOfJava(field.type()) != expectedSort
                    || !matchesEngineSymbol(raw,
                    SymbolicSourceEvidence.engineLabelForPhase(
                            sourcePhaseId, sourceId))) {
                continue;
            }
            if (selected != null) return null;
            selected = new ConfiguredSourceMatch(sourcePhaseId, sourceId,
                    field.signature());
        }
        return selected;
    }

    private static List<JsonObject> containerBoundaryActions(
            String raw, List<JsonObject> actions) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonObject action : actions) {
            if (!executable(action)
                    || materializationSort(action) != Sort.REF) {
                continue;
            }
            String symbol = string(action, "symbol");
            List<JsonArray> paths = new ArrayList<>();
            paths.add(new JsonArray());
            if (array(action, "fieldPath").size() > 0) {
                paths.add(array(action, "fieldPath"));
            }
            for (JsonElement path : array(action, "fieldPaths")) {
                if (path.isJsonArray()) paths.add(path.getAsJsonArray());
            }
            boolean matched = false;
            for (JsonArray path : paths) {
                List<String> segments = stringList(path);
                if (segments.size() != path.size()) continue;
                String label = symbol + (segments.isEmpty() ? ""
                        : "." + String.join(".", segments));
                if (matchesEngineSymbol(raw, label)) {
                    matched = true;
                    break;
                }
            }
            if (matched) result.add(action);
        }
        result.sort(Comparator.comparing(value -> string(value, "symbol")));
        return result;
    }

    private static ReplaySupport classifyReplaySupport(
            Encoder encoder, Set<String> symbols, List<JsonObject> actions,
            JsonObject activation) {
        Set<String> writable = new LinkedHashSet<>();
        Set<String> unresolved = new LinkedHashSet<>();
        for (String symbol : symbols) {
            if ("N".equals(symbol) || "V".equals(symbol)) continue;
            SymbolNames names = encoder.names(symbol);
            if (names != null
                    && fixedNonNullPlaceholder(symbol, names.sort)) {
                continue;
            }
            ActionMatch action = names == null ? null
                    : materializationResolution(symbol, actions,
                    names.sort);
            ConfiguredSourceMatch source = names == null ? null
                    : configuredSourceResolution(symbol, activation,
                    names.sort);
            if (names != null && (action == null) != (source == null)) {
                writable.add(symbol);
                encoder.controlledSymbols.add(symbol);
                continue;
            }

            String representative = encoder
                    .materializableFieldRepresentative(
                            symbol, actions, activation);
            SymbolNames representativeNames = encoder.names(representative);
            ActionMatch representativeAction = representativeNames == null
                    ? null : materializationResolution(representative,
                    actions, representativeNames.sort);
            ConfiguredSourceMatch representativeSource =
                    representativeNames == null ? null
                    : configuredSourceResolution(representative, activation,
                    representativeNames.sort);
            if (representativeNames != null
                    && (representativeAction == null)
                    != (representativeSource == null)) {
                writable.add(representative);
                encoder.controlledSymbols.add(representative);
                continue;
            }

            // NON_BRANCH_SOLVER_PATH_CONTEXT proves dependency and aliasing,
            // but carries no exact concrete snapshot provenance. Therefore a
            // remaining symbol (including time/environment placeholders)
            // cannot be safely pinned here.
            unresolved.add(symbol);
        }
        return new ReplaySupport(writable, unresolved);
    }

    /**
     * Cheap worklist-side admission probe.  It shares the solver's exact
     * writable-root rules and performs no solve or external process launch.
     */
    static boolean hasLocallyWritableReplayRoot(
            JsonElement predicate, JsonObject activation) {
        if (predicate == null || activation == null) return false;
        try {
            List<JsonObject> actions = materializationActions(activation);
            JsonArray predicates = new JsonArray();
            predicates.add(predicate.deepCopy());
            JsonArray context = new JsonArray();
            SparseContainerBoundaries boundaries =
                    SparseContainerBoundaries.discover(
                            predicates, context, actions);
            Encoder probe = new Encoder(boundaries);
            Set<String> symbols = probe.addConstraint(predicate,
                    "q_local_writable_probe");
            ReplaySupport support = classifyReplaySupport(
                    probe, symbols, actions, activation);
            return !support.writableSymbols.isEmpty()
                    || !boundaries.models.isEmpty();
        } catch (IOException malformedActions) {
            return false;
        }
    }

    private static boolean targetReachQuery(JsonObject task) {
        return ClosureGoalKind.TARGET_REACH_CLOSURE.name().equals(
                string(task, ClosureGoalKind.TASK_FIELD));
    }

    private static void collectEngineSymbols(
            JsonElement expression, Set<String> result) {
        if (expression == null || expression.isJsonNull()) return;
        if (expression.isJsonArray()) {
            for (JsonElement element : expression.getAsJsonArray()) {
                collectEngineSymbols(element, result);
            }
            return;
        }
        if (!expression.isJsonObject()) return;
        JsonObject object = expression.getAsJsonObject();
        if ("SymbolExpression".equals(string(object, "_type"))) {
            String raw = string(object, "_exp");
            if (!raw.isEmpty() && !"N".equals(raw) && !"V".equals(raw)) {
                result.add(raw);
            }
        }
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            collectEngineSymbols(entry.getValue(), result);
        }
    }

    /**
     * Branch predicates, rather than every semantic support expression in
     * the PC, define replay's writable inputs. Every predicate in the
     * contract participates: a later worklist wave still restarts from the
     * fixed workload seed and must reconstruct the previously discovered
     * prefix before it can flip the selected decision.
     */
    static Set<String> replayControlFrontier(
            List<Set<String>> branchSymbols) {
        Set<String> result = new LinkedHashSet<>();
        if (branchSymbols == null) return result;
        for (Set<String> predicate : branchSymbols) {
            result.addAll(predicate);
        }
        return result;
    }

    private static boolean containsNullReference(JsonElement expression) {
        if (expression == null || expression.isJsonNull()) return false;
        if (expression.isJsonArray()) {
            for (JsonElement element : expression.getAsJsonArray()) {
                if (containsNullReference(element)) return true;
            }
            return false;
        }
        if (!expression.isJsonObject()) return false;
        JsonObject object = expression.getAsJsonObject();
        if ("SymbolExpression".equals(string(object, "_type"))
                && "N".equals(string(object, "_exp"))) {
            return true;
        }
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            if (containsNullReference(entry.getValue())) return true;
        }
        return false;
    }

    /**
     * Null is a legal replay value only for the exact reference operand of a
     * witnessed null comparison.  A null literal elsewhere in the query must
     * not widen every reference domain.
     */
    static Set<String> referencesComparedWithNull(JsonArray constraints) {
        Set<String> result = new LinkedHashSet<>();
        if (constraints != null) {
            for (JsonElement constraint : constraints) {
                collectReferencesComparedWithNull(constraint, result);
            }
        }
        return result;
    }

    private static void collectReferencesComparedWithNull(
            JsonElement expression, Set<String> result) {
        if (expression == null || expression.isJsonNull()) return;
        if (expression.isJsonArray()) {
            for (JsonElement element : expression.getAsJsonArray()) {
                collectReferencesComparedWithNull(element, result);
            }
            return;
        }
        if (!expression.isJsonObject()) return;
        JsonObject object = expression.getAsJsonObject();
        if ("BinaryExpression".equals(string(object, "_type"))
                && ("==".equals(string(object, "_op"))
                || "!=".equals(string(object, "_op")))) {
            JsonElement left = object.get("_left");
            JsonElement right = object.get("_right");
            boolean leftNull = containsNullReference(left);
            boolean rightNull = containsNullReference(right);
            if (leftNull != rightNull) {
                collectReferenceSymbols(leftNull ? right : left, result);
            }
        }
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            collectReferencesComparedWithNull(entry.getValue(), result);
        }
    }

    private static void collectReferenceSymbols(
            JsonElement expression, Set<String> result) {
        if (expression == null || expression.isJsonNull()) return;
        if (expression.isJsonArray()) {
            for (JsonElement element : expression.getAsJsonArray()) {
                collectReferenceSymbols(element, result);
            }
            return;
        }
        if (!expression.isJsonObject()) return;
        JsonObject object = expression.getAsJsonObject();
        if ("SymbolExpression".equals(string(object, "_type"))) {
            String raw = string(object, "_exp");
            if (!raw.isEmpty() && !"N".equals(raw)) result.add(raw);
            return;
        }
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            collectReferenceSymbols(entry.getValue(), result);
        }
    }

    private static Map<String, List<JsonObject>> referenceActionsByDomain(
            List<JsonObject> actions) {
        Map<String, List<JsonObject>> result = new LinkedHashMap<>();
        for (JsonObject action : actions) {
            String key = referenceDomainKey(action);
            if (!key.isEmpty()) {
                result.computeIfAbsent(key,
                        ignored -> new ArrayList<>()).add(action);
            }
        }
        for (List<JsonObject> group : result.values()) {
            group.sort(Comparator.comparing(
                    value -> string(value, "symbol")));
        }
        return result;
    }

    private static String referenceDomainKey(JsonObject action) {
        if (!executable(action)
                || materializationSort(action) != Sort.REF
                || !"FIELD_ACCESS".equals(string(action, "bindingMode"))
                || !"HEAP_OBJECT_FIELD".equals(string(action, "location"))
                || longInteger(action, "fieldReceiverObjectId", 0L) <= 0L
                || longInteger(action, "valueObjectId", 0L) <= 0L
                || array(action, "fieldPath").size() != 1) {
            return "";
        }
        return longInteger(action, "fieldReceiverObjectId", 0L) + "\u0000"
                + JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                string(action, "javaType"));
    }

    private static Sort materializationSort(JsonObject action) {
        String javaType = string(action, "javaType");
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
                || payload.startsWith(semantic + "_");
    }


    private static boolean executable(JsonObject action) {
        return "SYMBOLIC".equals(string(action, "mode"));
    }

    private static final class ActionMatch {
        private final JsonObject action;
        private final List<String> path;

        private ActionMatch(JsonObject action, List<String> path) {
            this.action = action;
            this.path = new ArrayList<>(path);
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
        ProcessBuilder builder = new ProcessBuilder(executable.toString(),
                "-in", "-smt2");
        builder.redirectErrorStream(true);
        Process process = builder.start();
        try (OutputStream stream = process.getOutputStream()) {
            stream.write(input.getBytes(StandardCharsets.UTF_8));
        }
        boolean finished = process.waitFor(timeoutMillis,
                TimeUnit.MILLISECONDS);
        if (!finished) {
            process.destroyForcibly();
            process.waitFor();
            return new SolverOutput(true, "");
        }
        String stdout = readAll(process.getInputStream());
        return new SolverOutput(false, stdout);
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

    static Map<String, String> getValues(String output) {
        return parseGetValues(output);
    }

    private static Map<String, String> parseGetValues(String output) {
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

    private static boolean isJavaParseInt(String name) {
        return "java/lang/Integer parseInt".equals(firstNonBlank(name));
    }

    private static boolean isJavaSplitElement(String name) {
        return "java/lang/String splitElement".equals(firstNonBlank(name));
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

    /**
     * A VM {@code PlaceHolderSymbolExp} is created from an already allocated
     * object and names only its runtime class.  It is therefore fixed support
     * state, not a writable replay input; the only identity fact carried by
     * this compact IR is that the referenced object is non-null.
     */
    private static boolean fixedNonNullPlaceholder(String raw, Sort sort) {
        return sort == Sort.REF && raw != null && raw.startsWith("P_L");
    }

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

    private static boolean numeric(Sort sort) {
        return sort == Sort.INT || sort.floating();
    }

    private static String comparison(String operator) {
        if ("<".equals(operator)) return "<";
        if ("<=".equals(operator)) return "<=";
        if (">".equals(operator)) return ">";
        if (">=".equals(operator)) return ">=";
        return "";
    }

    private static String arithmetic(String operator) {
        if ("+".equals(operator)) return "+";
        if ("-".equals(operator)) return "-";
        if ("*".equals(operator)) return "*";
        return "";
    }

    private static boolean arithmeticOperator(String operator) {
        return "+".equals(operator) || "-".equals(operator)
                || "*".equals(operator) || "@".equals(operator)
                || "/".equals(operator) || "%".equals(operator);
    }

    private static boolean bitwiseOperator(String operator) {
        return "&".equals(operator) || "|".equals(operator)
                || "^".equals(operator);
    }

    private static boolean shiftOperator(String operator) {
        return "<<".equals(operator) || ">>".equals(operator)
                || ">>>".equals(operator);
    }

    private static Sort castSort(String descriptor) {
        return sortOfJava(descriptor);
    }

    private static FloatingKind floatingKind(Sort sort) {
        if (sort == Sort.FLOAT32) return FloatingKind.JAVA_FLOAT;
        if (sort == Sort.FLOAT64) return FloatingKind.JAVA_DOUBLE;
        return FloatingKind.NONE;
    }

    private static String expressionJavaType(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return "";
        JsonObject object = expression.getAsJsonObject();
        return string("MethodExpression".equals(string(object, "_type"))
                ? object(object, "_res_exp") : object, "_java_type");
    }

    private static String constantPayload(String raw) {
        int second = raw.indexOf('_', raw.indexOf('_') + 1);
        return second < 0 ? raw : raw.substring(second + 1);
    }

    private static String quote(String value) {
        return "\"" + value.replace("\"", "\"\"") + "\"";
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

        private SymbolNames(String raw, Sort sort, IntegralWidth width) {
            this.sort = sort;
            this.width = width;
            String safe = safeName(raw);
            String suffix = safe + "__" + sha256(raw).substring(0, 10);
            solver = "sym__" + suffix;
            String nullableKind = sort == Sort.STRING ? "string"
                    : sort == Sort.REF ? "reference" : "";
            nullness = nullableKind.isEmpty() ? ""
                    : "sym__" + nullableKind + "_is_null__" + safe + "__"
                    + sha256(nullableKind + "-null\u0000" + raw)
                    .substring(0, 10);
            floatingBits = "sym__fpbits__" + suffix;
            floatingNaN = "sym__fpisnan__" + suffix;
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
