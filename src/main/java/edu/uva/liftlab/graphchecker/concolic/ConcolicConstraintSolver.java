package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.IntegralWidth;
import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.FloatingKind;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;

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
        Encoder encoder = new Encoder();
        BranchReplayContract replayContract = query.replayContract;
        JsonArray contextConstraints = query.pathContext.expressions();
        for (int index = 0; index < contextConstraints.size(); index++) {
            encoder.addConstraint(contextConstraints.get(index),
                    "q_context_" + index);
        }
        JsonArray branchConstraints = replayContract
                .requiredPathPredicates();
        Set<String> targetSymbols = Collections.emptySet();
        for (int index = 0; index < branchConstraints.size(); index++) {
            Set<String> symbols = encoder.addConstraint(
                    branchConstraints.get(index),
                    "q_branch_" + index);
            if (index + 1 == branchConstraints.size()) {
                targetSymbols = symbols;
            }
        }
        String smt = encoder.finish();
        JsonObject record = baseRecord(query.queryKey);
        record.add("unsupported", strings(encoder.unsupported));
        if (!encoder.unsupported.isEmpty()) {
            record.addProperty("status", "UNSUPPORTED");
            record.addProperty("reason", "UNSUPPORTED_EXPRESSION_IR");
            return new Result(record, smt, new JsonArray(),
                    replayContract);
        }

        List<JsonObject> actions = materializationActions(activation);
        if (hasMaterializationGap(targetSymbols, actions, true)) {
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason",
                    "FLIP_CONDITION_DEPENDS_ON_UNMATERIALIZABLE_SYMBOLS");
            return new Result(record, smt, new JsonArray(),
                    replayContract);
        }

        // Recursive object symbolization may name the same leaf twice.
        // A PC-proven alias needs no second runtime write target.
        Set<String> projectedControlledSymbols = new LinkedHashSet<>(
                encoder.controlledSymbols);
        projectedControlledSymbols.removeAll(
                encoder.derivedFieldAliases(actions));
        if (hasMaterializationGap(projectedControlledSymbols, actions,
                false)) {
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason",
                    "PATH_CONSTRAINT_DEPENDS_ON_UNMATERIALIZABLE_"
                            + "CONTROLLED_SYMBOLS");
            return new Result(record, smt, new JsonArray(),
                    replayContract);
        }

        // Preserve non-null prefix objects; materialize exact null references.
        Set<String> targetControlledSymbols = new LinkedHashSet<>(
                targetSymbols);
        targetControlledSymbols.retainAll(encoder.controlledSymbols);

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
        for (String raw : encoder.controlledSymbols) {
            if (targetControlledSymbols.contains(raw)
                    || encoder.names(raw).sort != Sort.REF) {
                continue;
            }
            String nullnessValue = values.get(
                    encoder.names(raw).nullness);
            if ("false".equals(nullnessValue)) {
                projectedControlledSymbols.remove(raw);
            }
            // A missing/non-Boolean nullness value intentionally leaves the
            // symbol projected. modelAssignments will omit it and the normal
            // all-path-input completeness check below will fail closed.
        }
        JsonArray assignments = modelAssignments(encoder, values, actions,
                projectedControlledSymbols);
        if (targetControlledSymbols.isEmpty()) {
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason", "NO_REGION_INPUT_SYMBOL_IN_QUERY");
        } else if (assignments.size() < projectedControlledSymbols.size()) {
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason",
                    "NOT_ALL_PATH_INPUT_SYMBOLS_HAVE_MATERIALIZATION_TARGETS");
        } else {
            record.addProperty("status", "SAT_MODEL_READY");
        }
        return new Result(record, smt, assignments, replayContract);
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

    private static final class Encoder {
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
        private Set<String> currentConstraintSymbols;

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
            return fromContainerTerm(ContainerSmtCodec.term(
                    expression, containerHost(origin)), origin);
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
                        return ContainerSmtCodec.term(
                                expression.getAsJsonObject(), this);
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
                            ? "(VInt " + value.text + ")"
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
                    Sort sort = sortOfJava(javaType);
                    if (sort == Sort.INT) {
                        return new ContainerSmtCodec.Term(
                                "(valueInt " + value.text + ")",
                                ContainerSmtCodec.Sort.INT,
                                JavaPrimitiveSmtSemantics.widthOfJavaType(
                                        javaType));
                    }
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
                            + owner.text + ")", result));
                }

                @Override
                public void unsupported(String reason) {
                    Encoder.this.unsupported.add(origin + ":" + reason);
                }
            };
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
                    .primitiveTargetDescriptor(firstNonBlank(
                            string(expression, "targetJavaType"),
                            string(expression, "_java_type")), sourceType);
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
            String operator = string(expression, "_op");
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
            if (!regionInput(raw)) return;
            fieldSymbols.computeIfAbsent(CanonicalJson.render(field),
                    ignored -> new LinkedHashSet<>()).add(raw);
        }

        private Set<String> derivedFieldAliases(
                List<JsonObject> actions) {
            Set<String> result = new LinkedHashSet<>();
            for (Set<String> aliases : fieldSymbols.values()) {
                boolean hasTarget = false;
                for (String alias : aliases) {
                    if (materializationResolution(alias, actions) != null) {
                        hasTarget = true;
                        break;
                    }
                }
                if (!hasTarget) continue;
                for (String alias : aliases) {
                    if (materializationResolution(alias, actions) == null) {
                        result.add(alias);
                    }
                }
            }
            return result;
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
            unsupported.add(origin + ":METHOD_SEMANTICS_MISSING:" + method);
            return null;
        }

        private String finish() {
            StringBuilder result = new StringBuilder();
            result.append("(set-option :produce-models true)\n");
            result.append("(set-logic ALL)\n");
            result.append("(declare-sort Ref 0)\n");
            result.append("(declare-const nullRef Ref)\n");
            result.append("(declare-datatypes () ((Value"
                    + " (VInt (valueInt Int))"
                    + " (VFloat (valueFloat (_ FloatingPoint 8 24)))"
                    + " (VDouble (valueDouble (_ FloatingPoint 11 53)))"
                    + " (VBool (valueBool Bool))"
                    + " (VRef (valueRef Ref))"
                    + " (VString (valueString String)))))\n");
            for (String declaration : ContainerSmtCodec.preamble()) {
                result.append(declaration).append('\n');
            }
            result.append(JavaPrimitiveSmtSemantics.INT_WRAP_DEFINITION)
                    .append('\n');
            result.append(JavaPrimitiveSmtSemantics.LONG_WRAP_DEFINITION)
                    .append('\n');
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

    private static JsonArray modelAssignments(Encoder encoder,
                                              Map<String, String> values,
                                              List<JsonObject> actions,
                                              Set<String> projectedSymbols)
            {
        JsonArray result = new JsonArray();
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
            // A concrete non-null Java object cannot be reconstructed from
            // the SMT Ref sort.  Prefix reference guards are deliberately
            // kept out of projectedSymbols above and replayed from the source
            // object.  A target reference is materializable exactly when the
            // model selects null, which has a real runtime action.
            if (reference && !"true".equals(nullValue)) continue;
            ActionMatch match = materializationResolution(raw, actions);
            if (match == null) continue;
            JsonObject assignment = new JsonObject();
            assignment.addProperty("engineSymbol", raw);
            assignment.addProperty("solverSymbol", solverName);
            if (sort == Sort.STRING) {
                assignment.addProperty("nullnessSolverSymbol",
                        names.nullness);
                assignment.addProperty("modelIsNull",
                        "true".equals(nullValue));
            } else if (reference) {
                assignment.addProperty("nullnessSolverSymbol",
                        names.nullness);
                assignment.addProperty("modelIsNull", true);
            }
            assignment.addProperty("inputSymbol", string(match.action,
                    "symbol"));
            if (reference) {
                assignment.addProperty("valueType", "NULL");
                assignment.addProperty("value", "null");
                assignment.addProperty("referenceNullnessEncodingAuthority",
                        "JAVA_REFERENCE_NULLNESS_AS_EXACT_REF_EQUALITY_V1");
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
                assignment.addProperty("nullableStringEncodingAuthority",
                        "JAVA_STRING_CONTENT_PLUS_EXPLICIT_NULLNESS_BOOL_V1");
            } else {
                assignment.addProperty("valueType", sort.name());
                assignment.addProperty("value",
                        SmtModelValueCodec.normalizeScalar(value));
                if (sort == Sort.STRING) {
                    assignment.addProperty(
                            "nullableStringEncodingAuthority",
                            "JAVA_STRING_CONTENT_PLUS_EXPLICIT_"
                                    + "NULLNESS_BOOL_V1");
                }
            }
            assignment.addProperty("authority", "Z3_PATH_FLIP_MODEL");
            assignment.addProperty("materializeAtRealDefinition", true);
            assignment.add("target", match.action);
            List<String> actionPath = stringList(array(match.action,
                    "fieldPath"));
            List<String> replayPath = !match.path.isEmpty()
                    ? match.path : actionPath;
            if (!replayPath.isEmpty()) {
                assignment.add("materializationPath",
                        strings(replayPath));
            }
            result.add(assignment);
        }
        return result;
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

        private PathQuery(String queryKey,
                          BranchReplayContract replayContract,
                          SolverPathContext pathContext) {
            this.queryKey = queryKey;
            this.replayContract = replayContract;
            this.pathContext = pathContext;
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
            try {
                return new PathQuery(queryKey,
                        BranchReplayContract.fromJson(
                        requiredObject(task, "replayContract")),
                        SolverPathContext.fromJson(requiredObject(task,
                                "solverPathContext")));
            } catch (IllegalArgumentException malformed) {
                throw new IOException("invalid canonical path task: "
                        + malformed.getMessage(), malformed);
            }
        }
    }

    private static ActionMatch bestAction(
            String raw, List<JsonObject> actions) {
        ActionMatch best = null;
        int bestLength = -1;
        for (JsonObject action : actions) {
            if (!executable(action)) continue;
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
            String raw, List<JsonObject> actions) {
        return bestAction(raw, actions);
    }

    private static boolean hasMaterializationGap(
            Set<String> symbols, List<JsonObject> actions,
            boolean requireRegionInput) {
        for (String symbol : symbols) {
            if ("N".equals(symbol) || "V".equals(symbol)) continue;
            if ((requireRegionInput && !regionInput(symbol))
                    || materializationResolution(symbol, actions) == null) {
                return true;
            }
        }
        return false;
    }

    private static boolean matchesEngineSymbol(
            String engine, String semantic) {
        if (engine == null || semantic == null || semantic.isEmpty()) {
            return false;
        }
        if (engine.equals(semantic)) return true;
        String payload = "";
        if (engine.length() > 10 && engine.charAt(0) == 'M'
                && engine.charAt(1) == '_'
                && "ZCBSIFJDL".indexOf(engine.charAt(2)) >= 0
                && engine.startsWith("_field_", 3)) {
            payload = engine.substring(10);
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

    private static Map<String, String> parseGetValues(String output) {
        Map<String, String> result = new LinkedHashMap<>();
        int newline = output.indexOf('\n');
        if (newline < 0) return result;
        List<String> rows = SmtModelValueCodec.applicationItems(
                output.substring(newline + 1).trim());
        if (rows == null) return result;
        for (String row : rows) {
            List<String> pair = SmtModelValueCodec.applicationItems(row);
            if (pair != null && pair.size() == 2
                    && pair.get(0).startsWith("sym__")) {
                result.put(pair.get(0), pair.get(1));
            }
        }
        return result;
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
                ".*REGION(?:[._-][A-Za-z0-9-]+)+[._-]in[._-][0-9]+.*");
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
