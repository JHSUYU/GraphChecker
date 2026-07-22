package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.IntegralWidth;
import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.FloatingKind;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;

/**
 * Solves one normalized concolic branch-flip query and maps scalar model values
 * back to region input materialization actions.
 *
 * <p>Unknown library calls retain a deterministic uninterpreted-function
 * rendering only for diagnostic SMT inspection.  They are also recorded as
 * unsupported, so the solver cannot turn missing Java semantics into a replay
 * candidate.</p>
 */
public final class ConcolicConstraintSolver {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().create();

    private ConcolicConstraintSolver() {
    }

    public static Result solve(JsonObject task, JsonObject activation,
                               Path z3, long timeoutMillis)
            throws IOException, InterruptedException {
        Encoder encoder = new Encoder();
        BranchReplayContract replayContract = replayContract(task);
        rejectRetiredReplayAliases(task);
        JsonArray constraints = replayContract.requiredPathPredicates();
        for (int index = 0; index < constraints.size(); index++) {
            encoder.addConstraint(constraints.get(index), "q" + index);
        }
        String smt = encoder.finish();
        JsonObject record = baseRecord(task);
        record.addProperty("branchReplayContractId",
                replayContract.contractId());
        record.addProperty("branchConstraintAuthority",
                "IMMUTABLE_BRANCH_REPLAY_CONTRACT_V1");
        record.addProperty("solver", "Z3_SMT2");
        record.addProperty("solverInputHash", sha256(smt));
        record.addProperty("uninterpretedFunctionCount",
                encoder.uninterpretedFunctions.size());
        record.addProperty("integralInputRangeConstraintCount",
                encoder.integralRangeConstrainedSymbols.size());
        record.addProperty("numericEncodingAuthority",
                "JAVA_PRIMITIVE_INPUT_BOUNDS_WITH_TWOS_COMPLEMENT_"
                        + "INT_LONG_ARITHMETIC_V2");
        record.addProperty("javaIntegralOverflowModeled", true);
        record.addProperty("ieee754FloatingPointModeled", true);
        record.addProperty("floatingPointEncodingAuthority",
                "JAVA_IEEE_754_BINARY32_BINARY64_RNE_WITH_"
                        + "UNSUPPORTED_OPERATIONS_FAIL_CLOSED_V1");
        record.addProperty("nullableJavaStringModeled", true);
        record.addProperty("nullableStringEncodingAuthority",
                "JAVA_STRING_CONTENT_PLUS_EXPLICIT_NULLNESS_BOOL_V1");
        record.addProperty("nullableJavaReferenceModeled", true);
        record.addProperty("referenceNullnessEncodingAuthority",
                "JAVA_REFERENCE_NULLNESS_AS_EXACT_REF_EQUALITY_V1");
        record.addProperty("uncontrolledEnvironmentTermCount",
                encoder.uncontrolledEnvironmentTerms.size());
        record.add("uncontrolledEnvironmentTerms",
                GSON.toJsonTree(encoder.uncontrolledEnvironmentTerms));
        record.addProperty("environmentModelAssignmentCount", 0);
        record.addProperty("requiresUnforcedEnvironmentValidation",
                !encoder.uncontrolledEnvironmentTerms.isEmpty());
        record.add("unsupported", GSON.toJsonTree(encoder.unsupported));
        if (!encoder.unsupported.isEmpty()) {
            record.addProperty("status", "UNSUPPORTED");
            record.addProperty("reason", "UNSUPPORTED_EXPRESSION_IR");
            return new Result(record, smt, new JsonArray());
        }

        DynamicBindingRegistry dynamicBindings =
                DynamicBindingRegistry.from(task);
        record.addProperty("dynamicFieldBindingCount",
                dynamicBindings.bindings.size());
        if (!dynamicBindings.problems.isEmpty()) {
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason",
                    "INVALID_DYNAMIC_FIELD_BINDING_REGISTRY");
            record.add("dynamicFieldBindingProblems",
                    GSON.toJsonTree(dynamicBindings.problems));
            record.addProperty("solverInvoked", false);
            return new Result(record, smt, new JsonArray());
        }

        Set<String> targetSymbols = symbolicNames(targetConstraint(task));
        Set<String> unmaterializableTargetSymbols = new LinkedHashSet<>();
        Set<String> targetResolutionGaps = new LinkedHashSet<>();
        MaterializationActionCatalog actions =
                materializationActions(activation);
        for (String raw : targetSymbols) {
            MaterializationResolution resolution =
                    materializationResolution(raw, actions,
                            dynamicBindings);
            if (!"N".equals(raw) && !"V".equals(raw)
                    && (!regionInput(raw) || !resolution.resolved())) {
                unmaterializableTargetSymbols.add(raw);
                if (!resolution.gap.isEmpty()) {
                    targetResolutionGaps.add(raw + ":" + resolution.gap);
                }
            }
        }
        record.add("flipConditionSymbols",
                GSON.toJsonTree(targetSymbols));
        if (!unmaterializableTargetSymbols.isEmpty()) {
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason",
                    "FLIP_CONDITION_DEPENDS_ON_UNMATERIALIZABLE_SYMBOLS");
            record.add("unmaterializableFlipSymbols",
                    GSON.toJsonTree(unmaterializableTargetSymbols));
            if (!targetResolutionGaps.isEmpty()) {
                record.add("dynamicBindingResolutionGaps",
                        GSON.toJsonTree(targetResolutionGaps));
            }
            record.addProperty("solverInvoked", false);
            return new Result(record, smt, new JsonArray());
        }

        // Replaying a later path flip must reproduce every symbolic prefix
        // decision naturally.  Projecting only symbols mentioned by the
        // flipped condition is insufficient when the source path itself was
        // reached with a model (rather than the workload's original concrete
        // arguments): the omitted prefix input then falls back to an unrelated
        // seed value and the exact-prefix replay is guaranteed to drift.
        // Require a real materialization target for every solver-controlled
        // region input before invoking Z3.  Environment terms remain
        // deliberately unforced and are validated separately.
        Set<String> unmaterializableControlledSymbols =
                new LinkedHashSet<>();
        Set<String> controlledResolutionGaps = new LinkedHashSet<>();
        for (String raw : encoder.controlledSymbols) {
            MaterializationResolution resolution =
                    materializationResolution(raw, actions,
                            dynamicBindings);
            if (!resolution.resolved()) {
                unmaterializableControlledSymbols.add(raw);
                if (!resolution.gap.isEmpty()) {
                    controlledResolutionGaps.add(raw + ":"
                            + resolution.gap);
                }
            }
        }
        if (!unmaterializableControlledSymbols.isEmpty()) {
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason",
                    "PATH_CONSTRAINT_DEPENDS_ON_UNMATERIALIZABLE_"
                            + "CONTROLLED_SYMBOLS");
            record.add("unmaterializableControlledSymbols",
                    GSON.toJsonTree(unmaterializableControlledSymbols));
            if (!controlledResolutionGaps.isEmpty()) {
                record.add("dynamicBindingResolutionGaps",
                        GSON.toJsonTree(controlledResolutionGaps));
            }
            record.addProperty("solverInvoked", false);
            return new Result(record, smt, new JsonArray());
        }

        // Reference prefix inputs are partitioned after reading the model.
        // A non-null prefix can preserve the source activation's real object
        // and rely on exact ordered-prefix validation.  A null prefix cannot:
        // it must be materialized as an explicit NULL assignment so a later
        // branch flip replays the same path instead of silently restoring the
        // source object's non-null value.  Target references always remain
        // projected; null is materializable, while a requested non-null
        // object fails closed because this layer cannot fabricate one.
        Set<String> targetControlledSymbols = new LinkedHashSet<>(
                targetSymbols);
        targetControlledSymbols.retainAll(encoder.controlledSymbols);
        Set<String> projectedControlledSymbols = new LinkedHashSet<>(
                encoder.controlledSymbols);

        Path executable = z3 == null ? Paths.get("z3") : z3;
        SolverOutput output = run(executable, smt,
                Math.max(1L, timeoutMillis));
        record.addProperty("solverExitCode", output.exitCode);
        record.addProperty("solverInvoked", true);
        record.addProperty("solverTimedOut", output.timedOut);
        record.addProperty("solverStderr", output.stderr.trim());
        if (output.timedOut) {
            record.addProperty("status", "SOLVER_ERROR");
            record.addProperty("reason", "SOLVER_TIMEOUT");
            return new Result(record, smt, new JsonArray());
        }
        String status = firstLine(output.stdout);
        record.addProperty("solverStatus", status);
        if ("unsat".equals(status)) {
            record.addProperty("status", "UNSAT");
            return new Result(record, smt, new JsonArray());
        }
        if (!"sat".equals(status)) {
            record.addProperty("status", "SOLVER_ERROR");
            record.addProperty("reason", firstNonBlank(status,
                    "NO_SOLVER_STATUS"));
            return new Result(record, smt, new JsonArray());
        }

        Map<String, String> values = parseGetValues(output.stdout);
        Set<String> unforcedPrefixReferenceSymbols = new LinkedHashSet<>();
        Set<String> materializedNullPrefixReferenceSymbols =
                new LinkedHashSet<>();
        for (String raw : encoder.controlledSymbols) {
            if (targetControlledSymbols.contains(raw)
                    || encoder.rawToSort.get(raw) != Sort.REF) {
                continue;
            }
            String nullnessName = encoder.rawToReferenceNullName.get(raw);
            String nullnessValue = nullnessName == null ? null
                    : values.get(nullnessName);
            if ("false".equals(nullnessValue)) {
                unforcedPrefixReferenceSymbols.add(raw);
                projectedControlledSymbols.remove(raw);
            } else if ("true".equals(nullnessValue)) {
                materializedNullPrefixReferenceSymbols.add(raw);
            }
            // A missing/non-Boolean nullness value intentionally leaves the
            // symbol projected. modelAssignments will omit it and the normal
            // all-path-input completeness check below will fail closed.
        }
        record.addProperty("unforcedPrefixReferenceSymbolCount",
                unforcedPrefixReferenceSymbols.size());
        record.add("unforcedPrefixReferenceSymbols",
                GSON.toJsonTree(unforcedPrefixReferenceSymbols));
        record.addProperty("unforcedPrefixReferenceAuthority",
                "SOURCE_NON_NULL_REFERENCE_PRESERVATION_PLUS_EXACT_"
                        + "ORDERED_PREFIX_REPLAY_VALIDATION_V2");
        record.addProperty("materializedNullPrefixReferenceSymbolCount",
                materializedNullPrefixReferenceSymbols.size());
        record.add("materializedNullPrefixReferenceSymbols",
                GSON.toJsonTree(materializedNullPrefixReferenceSymbols));
        record.addProperty("nullPrefixReferenceMaterializationAuthority",
                "Z3_EXACT_REFERENCE_NULLNESS_TO_RUNTIME_NULL_"
                        + "MATERIALIZATION_V1");
        if (!unforcedPrefixReferenceSymbols.isEmpty()) {
            record.addProperty("requiresUnforcedEnvironmentValidation", true);
        }
        Set<String> unforcedPrefixSymbols = new LinkedHashSet<>(
                projectedControlledSymbols);
        unforcedPrefixSymbols.removeAll(targetControlledSymbols);
        JsonArray assignments = modelAssignments(encoder, values,
                activation, dynamicBindings, projectedControlledSymbols);
        record.add("modelAssignments", assignments.deepCopy());
        record.addProperty("modelAssignmentCount", assignments.size());
        record.addProperty("modelProjectionPolicy",
                "FULL_PATH_MATERIALIZABLE_INPUTS_PLUS_MODEL_"
                        + "PARTITIONED_PREFIX_REFERENCES_V4");
        record.addProperty("controlledSymbolCount",
                encoder.controlledSymbols.size());
        record.addProperty("targetControlledSymbolCount",
                targetControlledSymbols.size());
        record.addProperty("materializedPrefixControlledSymbolCount",
                unforcedPrefixSymbols.size());
        record.add("materializedPrefixControlledSymbols",
                GSON.toJsonTree(unforcedPrefixSymbols));
        record.addProperty("modelUsedOnlyForReplay", true);
        record.addProperty("branchOverrideAllowed", false);
        if (targetControlledSymbols.isEmpty()) {
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason", "NO_REGION_INPUT_SYMBOL_IN_QUERY");
        } else if (assignments.size() < projectedControlledSymbols.size()) {
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason",
                    "NOT_ALL_PATH_INPUT_SYMBOLS_HAVE_MATERIALIZATION_TARGETS");
            record.add("unmappedInputSymbols", GSON.toJsonTree(
                    unmapped(projectedControlledSymbols, assignments)));
            Set<String> resolutionGaps = new LinkedHashSet<>();
            for (String raw : unmapped(projectedControlledSymbols,
                    assignments)) {
                MaterializationResolution resolution =
                        materializationResolution(raw, actions,
                                dynamicBindings);
                if (!resolution.gap.isEmpty()) {
                    resolutionGaps.add(raw + ":" + resolution.gap);
                }
            }
            if (!resolutionGaps.isEmpty()) {
                record.add("dynamicBindingResolutionGaps",
                        GSON.toJsonTree(resolutionGaps));
            }
        } else {
            record.addProperty("status", "SAT_MODEL_READY");
        }
        return new Result(record, smt, assignments);
    }

    public static final class Result {
        public final JsonObject record;
        public final String smtLib;
        public final JsonArray modelAssignments;

        private Result(JsonObject record, String smtLib,
                       JsonArray modelAssignments) {
            this.record = record;
            this.smtLib = smtLib;
            this.modelAssignments = modelAssignments;
        }
    }

    private static final class Encoder {
        private final Map<String, Sort> declarations = new LinkedHashMap<>();
        private final Map<String, String> rawToName = new LinkedHashMap<>();
        private final Map<String, Sort> rawToSort = new LinkedHashMap<>();
        /**
         * Java String inputs have both reference nullability and character
         * contents.  SMT-LIB String represents only the latter, so every
         * controlled String symbol gets a companion Bool instead of
         * conflating Java null with either an SMT string or {@code nullRef}.
         */
        private final Map<String, String> rawToStringNullName =
                new LinkedHashMap<>();
        /** Exact null predicate for non-String Java reference inputs. */
        private final Map<String, String> rawToReferenceNullName =
                new LinkedHashMap<>();
        private final Map<String, IntegralWidth> rawToIntegralWidth =
                new LinkedHashMap<>();
        private final Map<String, String> rawToModelName =
                new LinkedHashMap<>();
        private final Map<String, String> rawToModelNaNName =
                new LinkedHashMap<>();
        private final List<String> assertions = new ArrayList<>();
        private final Set<String> unsupported = new LinkedHashSet<>();
        private final Set<String> uninterpretedFunctions =
                new LinkedHashSet<>();
        private final Set<String> controlledSymbols = new LinkedHashSet<>();
        private final Set<String> uncontrolledEnvironmentTerms =
                new LinkedHashSet<>();
        private final Set<String> integralRangeConstrainedSymbols =
                new LinkedHashSet<>();
        private final Map<String, FunctionSignature> functions =
                new LinkedHashMap<>();

        private void addConstraint(JsonElement expression, String origin) {
            if (expression == null || !expression.isJsonObject()) {
                unsupported.add(origin + ":NON_OBJECT_EXPRESSION");
                return;
            }
            JsonObject object = expression.getAsJsonObject();
            String type = string(object, "_type");
            if ("MethodExpression".equals(type)) {
                String constraint = methodConstraint(object, origin);
                if (!constraint.isEmpty()) assertions.add(constraint);
                return;
            }
            if ("_array_expr".equals(type)) {
                String constraint = arrayConstraint(object, origin);
                if (!constraint.isEmpty()) assertions.add(constraint);
                return;
            }
            Term term = term(expression, null, origin);
            if (term != null && term.sort == Sort.BOOL) {
                assertions.add(term.text);
            } else if (term != null) {
                unsupported.add(origin + ":NON_BOOLEAN_CONSTRAINT");
            }
        }

        private Term term(JsonElement expression, Sort expected,
                          String origin) {
            if (expression == null || expression.isJsonNull()
                    || !expression.isJsonObject()) {
                return new Term("nullRef", Sort.REF);
            }
            JsonObject object = expression.getAsJsonObject();
            String type = string(object, "_type");
            if ("SymbolExpression".equals(type)
                    || "ConSymbolExp".equals(type)) {
                return symbol(object, expected);
            }
            if ("ConstExpr".equals(type)
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
            unsupported.add(origin + ":TYPE:" + firstNonBlank(type,
                    "MISSING"));
            return null;
        }

        private Term symbol(JsonObject expression, Sort expected) {
            String raw = string(expression, "_exp");
            if ("N".equals(raw)) return new Term("nullRef", Sort.REF);
            if ("V".equals(raw)) return new Term("true", Sort.BOOL);
            String javaType = string(expression, "_java_type");
            Sort declaredSort = sortOfJava(javaType);
            Sort sort = declaredSort != Sort.UNKNOWN ? declaredSort
                    : expected == null ? Sort.UNKNOWN : expected;
            if (sort == Sort.UNKNOWN) sort = Sort.REF;
            IntegralWidth width = JavaPrimitiveSmtSemantics
                    .widthOfJavaType(javaType);
            String name = rawToName.get(raw);
            if (name == null) {
                name = "sym__" + safeName(raw) + "__"
                        + sha256(raw).substring(0, 10);
                rawToName.put(raw, name);
                rawToSort.put(raw, sort);
                rawToIntegralWidth.put(raw, width);
                declarations.put(name, sort);
                if (sort == Sort.STRING) {
                    String nullName = "sym__string_is_null__"
                            + safeName(raw) + "__"
                            + sha256("string-null\u0000" + raw)
                            .substring(0, 10);
                    rawToStringNullName.put(raw, nullName);
                    declarations.put(nullName, Sort.BOOL);
                } else if (sort == Sort.REF) {
                    String nullName = "sym__reference_is_null__"
                            + safeName(raw) + "__"
                            + sha256("reference-null\u0000" + raw)
                            .substring(0, 10);
                    rawToReferenceNullName.put(raw, nullName);
                }
                if (regionInput(raw)) controlledSymbols.add(raw);
                constrainIntegralInput(raw, name, javaType, sort);
            } else {
                Sort previousSort = rawToSort.get(raw);
                IntegralWidth previousWidth = rawToIntegralWidth.get(raw);
                if (previousSort != sort) {
                    unsupported.add("SYMBOL_SORT_CONFLICT:" + raw + ":"
                            + previousSort + "->" + sort);
                }
                if (previousWidth != null && width != IntegralWidth.NONE
                        && previousWidth != IntegralWidth.NONE
                        && previousWidth != width) {
                    unsupported.add("SYMBOL_INTEGRAL_WIDTH_CONFLICT:" + raw
                            + ":" + previousWidth + "->" + width);
                }
            }
            IntegralWidth actualWidth = rawToIntegralWidth.get(raw);
            Sort actualSort = rawToSort.get(raw);
            if (actualSort == Sort.STRING) {
                return Term.javaString(name,
                        rawToStringNullName.get(raw), raw);
            }
            return new Term(name, actualSort, actualWidth);
        }

        private void constrainIntegralInput(String raw, String name,
                                            String javaType, Sort sort) {
            if (sort != Sort.INT) return;
            JavaPrimitiveSmtSemantics.IntegralDomain domain =
                    JavaPrimitiveSmtSemantics.domainOfJavaType(javaType);
            if (domain == null
                    || !integralRangeConstrainedSymbols.add(raw)) return;
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
            uncontrolledEnvironmentTerms.add(identity);
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
                String literal = integerLiteral(payload);
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
            String name = "const__" + safeName(raw) + "__"
                    + sha256(raw).substring(0, 8);
            declarations.put(name, Sort.REF);
            return new Term(name, Sort.REF);
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
            String sourceType = castDescriptor(
                    firstNonBlank(string(expression, "sourceJavaType"),
                            expressionJavaType(sourceExpression)));
            String targetType = castTargetDescriptor(firstNonBlank(
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
                return diagnosticTerm("unsupported_cast", origin,
                        targetSort == Sort.UNKNOWN ? Sort.REF : targetSort);
            }
            unsupported.add(origin + ":UNSUPPORTED_JAVA_CAST:"
                    + firstNonBlank(sourceType, "UNKNOWN") + "->"
                    + firstNonBlank(targetType, "UNKNOWN"));
            return diagnosticTerm("unsupported_cast", origin,
                    targetSort == Sort.UNKNOWN ? Sort.REF : targetSort);
        }

        private Term diagnosticTerm(String prefix, String origin, Sort sort) {
            String material = prefix + "\u0000" + origin + "\u0000" + sort;
            String name = prefix + "__" + safeName(origin) + "__"
                    + sha256(material).substring(0, 10);
            declarations.put(name, sort);
            return new Term(name, sort);
        }

        private Term binary(JsonObject expression, String origin) {
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
                    return diagnosticTerm("ambiguous_integral_unary",
                            origin, Sort.INT);
                }
                unsupported.add(origin + ":NON_NUMERIC_OR_UNKNOWN_UNARY:"
                        + firstNonBlank(operator, "MISSING"));
                return operand == null ? null : diagnosticTerm(
                        "unsupported_unary", origin, operand.sort);
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
                return diagnosticTerm("malformed_lcmp", origin, Sort.INT);
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
                return diagnosticTerm("malformed_fp_cmp", origin, Sort.INT);
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
                    return diagnosticTerm("unsupported_remainder", origin,
                            result);
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
                    return diagnosticTerm("unsupported_floating_arithmetic",
                            origin, result);
                }
                if ("@".equals(operator) || "/".equals(operator)) {
                    unsupported.add(origin
                            + ":JAVA_INTEGRAL_DIVISION_UNMODELED");
                    return diagnosticTerm("unsupported_division", origin,
                            Sort.INT);
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
                    return diagnosticTerm("ambiguous_integral_arithmetic",
                            origin, Sort.INT);
                }
                return new Term(JavaPrimitiveSmtSemantics.wrap(
                        arithmeticExpression, resultWidth), Sort.INT,
                        resultWidth);
            }
            unsupported.add(origin + ":BINARY_OPERATOR:" + operator);
            return null;
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
            Term result = term(expression.get("_res_exp"),
                    call == null ? null : call.sort, origin + ":result");
            if (call == null || result == null) return "";
            if (call.sort != result.sort) {
                unsupported.add(origin + ":METHOD_RESULT_SORT_MISMATCH");
                return "";
            }
            return "(= " + result.text + " " + call.text + ")";
        }

        private Term methodTerm(JsonObject expression, String origin) {
            String method = firstNonBlank(string(expression, "_name"),
                    "unknown_method");
            JsonArray parameters = array(expression, "_param_list");
            List<Term> arguments = new ArrayList<>();
            for (int index = 0; index < parameters.size(); index++) {
                Term argument = term(parameters.get(index), null,
                        origin + ":arg" + index);
                if (argument == null) return null;
                arguments.add(argument);
            }
            JsonObject resultExpression = object(expression, "_res_exp");
            Sort resultSort = sortOfJava(string(resultExpression,
                    "_java_type"));
            if (resultSort == Sort.UNKNOWN) resultSort = Sort.REF;
            String function = "uf__" + safeName(method) + "__"
                    + sha256(signature(method, arguments, resultSort))
                    .substring(0, 10);
            FunctionSignature signature = new FunctionSignature(arguments,
                    resultSort);
            FunctionSignature previous = functions.get(function);
            if (previous != null && !previous.equals(signature)) {
                unsupported.add(origin + ":INCONSISTENT_METHOD_SIGNATURE:"
                        + method);
                return null;
            }
            functions.put(function, signature);
            uninterpretedFunctions.add(function);
            // Retain the UF only so the diagnostic SMT remains inspectable.
            // No arbitrary Java call is an exact semantic adapter here, so a
            // replay candidate must never be confused with admitted meaning.
            unsupported.add(origin + ":METHOD_SEMANTICS_MISSING:" + method);
            StringBuilder call = new StringBuilder("(").append(function);
            for (Term argument : arguments) {
                call.append(' ').append(argument.text);
            }
            return new Term(call.append(')').toString(), resultSort);
        }

        private String arrayConstraint(JsonObject expression, String origin) {
            if (!bool(expression, "_is_load", false)) {
                unsupported.add(origin + ":ARRAY_STORE_UNSUPPORTED");
                return "";
            }
            Term index = term(expression.get("_index_exp"), Sort.INT,
                    origin + ":index");
            Term value = term(expression.get("_value_exp"), null,
                    origin + ":value");
            if (index == null || value == null) return "";
            String raw = string(expression, "_arr_str");
            String name = "array__" + safeName(raw) + "__"
                    + sha256(raw + value.sort).substring(0, 8);
            Sort arraySort = value.sort.arraySort();
            if (arraySort == Sort.UNKNOWN) {
                unsupported.add(origin + ":ARRAY_VALUE_SORT:" + value.sort);
                return "";
            }
            declarations.put(name, arraySort);
            return "(= " + value.text + " (select " + name + " "
                    + index.text + "))";
        }

        private String finish() {
            StringBuilder result = new StringBuilder();
            result.append("(set-option :produce-models true)\n");
            result.append("(set-logic ALL)\n");
            result.append("(declare-sort Ref 0)\n");
            result.append("(declare-const nullRef Ref)\n");
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
            for (Map.Entry<String, FunctionSignature> entry
                    : functions.entrySet()) {
                result.append("(declare-fun ").append(entry.getKey())
                        .append(" (");
                for (int index = 0;
                     index < entry.getValue().arguments.size(); index++) {
                    if (index > 0) result.append(' ');
                    result.append(entry.getValue().arguments.get(index).sort.smt);
                }
                result.append(") ").append(entry.getValue().result.smt)
                        .append(")\n");
            }
            for (Map.Entry<String, String> entry
                    : rawToReferenceNullName.entrySet()) {
                String reference = rawToName.get(entry.getKey());
                if (reference != null) {
                    result.append("(define-fun ").append(entry.getValue())
                            .append(" () Bool (= ").append(reference)
                            .append(" nullRef))\n");
                }
            }
            // Ask Z3 for both the IEEE bits and an explicit NaN discriminator.
            // SMT deliberately leaves fp.to_ieee_bv(NaN) unspecified (Z3
            // 4.8 may return all-zero bits), so replay must never interpret
            // that bit-vector unless the discriminator is false.
            for (String raw : controlledSymbols) {
                String name = rawToName.get(raw);
                Sort sort = rawToSort.get(raw);
                if (name == null || sort == null || !sort.floating()) {
                    continue;
                }
                String bits = "sym__fpbits__" + name.substring("sym__".length());
                String isNaN = "sym__fpisnan__"
                        + name.substring("sym__".length());
                rawToModelName.put(raw, bits);
                rawToModelNaNName.put(raw, isNaN);
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
                String name = rawToName.get(raw);
                Sort sort = rawToSort.get(raw);
                if (name != null && !sort.isArray()) {
                    if (sort.floating()) {
                        modelNames.add(rawToModelName.get(raw));
                        modelNames.add(rawToModelNaNName.get(raw));
                    } else if (sort == Sort.STRING) {
                        modelNames.add(name);
                        modelNames.add(rawToStringNullName.get(raw));
                    } else if (sort == Sort.REF) {
                        modelNames.add(rawToReferenceNullName.get(raw));
                    } else {
                        modelNames.add(name);
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
        REF("Ref"), INT_ARRAY("(Array Int Int)"),
        FLOAT32_ARRAY("(Array Int (_ FloatingPoint 8 24))"),
        FLOAT64_ARRAY("(Array Int (_ FloatingPoint 11 53))"),
        BOOL_ARRAY("(Array Int Bool)"),
        STRING_ARRAY("(Array Int String)"), REF_ARRAY("(Array Int Ref)"),
        UNKNOWN("");

        private final String smt;

        Sort(String smt) {
            this.smt = smt;
        }

        private Sort arraySort() {
            if (this == INT) return INT_ARRAY;
            if (this == FLOAT32) return FLOAT32_ARRAY;
            if (this == FLOAT64) return FLOAT64_ARRAY;
            if (this == BOOL) return BOOL_ARRAY;
            if (this == STRING) return STRING_ARRAY;
            if (this == REF) return REF_ARRAY;
            return UNKNOWN;
        }

        private boolean isArray() {
            return name().endsWith("_ARRAY");
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

    private static final class FunctionSignature {
        private final List<Term> arguments;
        private final Sort result;

        private FunctionSignature(List<Term> arguments, Sort result) {
            this.arguments = new ArrayList<>(arguments);
            this.result = result;
        }

        @Override
        public boolean equals(Object value) {
            if (!(value instanceof FunctionSignature)) return false;
            FunctionSignature other = (FunctionSignature) value;
            if (result != other.result
                    || arguments.size() != other.arguments.size()) return false;
            for (int index = 0; index < arguments.size(); index++) {
                if (arguments.get(index).sort != other.arguments.get(index).sort) {
                    return false;
                }
            }
            return true;
        }

        @Override
        public int hashCode() {
            int value = result.hashCode();
            for (Term argument : arguments) {
                value = value * 31 + argument.sort.hashCode();
            }
            return value;
        }
    }

    private static JsonArray modelAssignments(Encoder encoder,
                                              Map<String, String> values,
                                              JsonObject activation,
                                              DynamicBindingRegistry registry,
                                              Set<String> projectedSymbols) {
        JsonArray result = new JsonArray();
        MaterializationActionCatalog actions =
                materializationActions(activation);

        for (String raw : encoder.controlledSymbols) {
            if (!projectedSymbols.contains(raw)) continue;
            String solverName = encoder.rawToName.get(raw);
            Sort sort = encoder.rawToSort.get(raw);
            String modelName = firstNonBlank(encoder.rawToModelName.get(raw),
                    solverName);
            String value = values.get(modelName);
            String nanModelName = encoder.rawToModelNaNName.get(raw);
            String nanValue = nanModelName == null ? ""
                    : values.get(nanModelName);
            String stringNullModelName = sort == Sort.STRING
                    ? encoder.rawToStringNullName.get(raw) : "";
            String stringNullValue = stringNullModelName == null
                    || stringNullModelName.isEmpty() ? ""
                    : values.get(stringNullModelName);
            String referenceNullModelName = sort == Sort.REF
                    ? encoder.rawToReferenceNullName.get(raw) : "";
            String referenceNullValue = referenceNullModelName == null
                    || referenceNullModelName.isEmpty() ? ""
                    : values.get(referenceNullModelName);
            boolean reference = sort == Sort.REF;
            if ((!reference && value == null) || sort.isArray()
                    || sort.floating() && !("true".equals(nanValue)
                    || "false".equals(nanValue))
                    || sort == Sort.STRING
                    && !("true".equals(stringNullValue)
                    || "false".equals(stringNullValue))
                    || reference
                    && !("true".equals(referenceNullValue)
                    || "false".equals(referenceNullValue))) continue;
            // A concrete non-null Java object cannot be reconstructed from
            // the SMT Ref sort.  Prefix reference guards are deliberately
            // kept out of projectedSymbols above and replayed from the source
            // object.  A target reference is materializable exactly when the
            // model selects null, which has a real runtime action.
            if (reference && !"true".equals(referenceNullValue)) continue;
            MaterializationResolution resolution =
                    materializationResolution(raw, actions, registry);
            if (!resolution.resolved()) continue;
            ActionMatch match = resolution.action;
            JsonObject assignment = new JsonObject();
            assignment.addProperty("engineSymbol", raw);
            assignment.addProperty("solverSymbol", solverName);
            if (sort == Sort.STRING) {
                assignment.addProperty("nullnessSolverSymbol",
                        stringNullModelName);
                assignment.addProperty("modelIsNull",
                        "true".equals(stringNullValue));
            } else if (reference) {
                assignment.addProperty("nullnessSolverSymbol",
                        referenceNullModelName);
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
                assignment.addProperty("floatingPointFormat", descriptor);
                assignment.addProperty("modelNaNSymbol", nanModelName);
                assignment.addProperty("modelIsNaN", isNaN);
                if (isNaN) {
                    assignment.addProperty("nanReplayAuthority",
                            "SMT_FP_IS_NAN_TO_JAVA_CANONICAL_NAN_V1");
                } else {
                    assignment.addProperty("modelBitSymbol", modelName);
                    assignment.addProperty("modelIeeeBits", value);
                }
                assignment.addProperty("value", decoded);
            } else if (sort == Sort.STRING
                    && "true".equals(stringNullValue)) {
                assignment.addProperty("valueType", "NULL");
                assignment.addProperty("value", "null");
                assignment.addProperty("nullableStringEncodingAuthority",
                        "JAVA_STRING_CONTENT_PLUS_EXPLICIT_NULLNESS_BOOL_V1");
            } else {
                assignment.addProperty("valueType", sort.name());
                assignment.addProperty("value", normalizeModelValue(value));
                if (sort == Sort.STRING) {
                    assignment.addProperty(
                            "nullableStringEncodingAuthority",
                            "JAVA_STRING_CONTENT_PLUS_EXPLICIT_"
                                    + "NULLNESS_BOOL_V1");
                }
            }
            assignment.addProperty("authority", "Z3_PATH_FLIP_MODEL");
            assignment.addProperty("materializeAtRealDefinition", true);
            assignment.add("target", match.action.deepCopy());
            List<String> actionPath = stringList(array(match.action,
                    "fieldPath"));
            List<String> replayPath = !match.path.isEmpty()
                    ? match.path : actionPath;
            if (!replayPath.isEmpty()) {
                assignment.add("materializationPath",
                        GSON.toJsonTree(replayPath));
            }
            if (resolution.binding != null) {
                resolution.binding.copySelectorTo(assignment);
                List<String> bindingPath = resolution.binding.fieldPath();
                if (!bindingPath.isEmpty()) {
                    assignment.add("materializationPath",
                            GSON.toJsonTree(bindingPath));
                }
            }
            result.add(assignment);
        }
        return result;
    }

    private static MaterializationActionCatalog materializationActions(
            JsonObject activation) {
        List<JsonObject> executable = new ArrayList<>();
        JsonArray materializations = array(activation, "materializations");
        JsonArray source = materializations.size() > 0
                ? materializations : array(activation, "symbolize");
        for (JsonElement element : source) {
            if (element.isJsonObject()) {
                executable.add(element.getAsJsonObject());
            }
        }
        List<JsonObject> declared = new ArrayList<>();
        for (JsonElement element : array(activation, "symbolize")) {
            if (element.isJsonObject()) {
                declared.add(element.getAsJsonObject());
            }
        }
        Comparator<JsonObject> bySymbol = Comparator.comparing(
                value -> string(value, "symbol"));
        Collections.sort(executable, bySymbol);
        Collections.sort(declared, bySymbol);
        return new MaterializationActionCatalog(executable, declared);
    }

    private static JsonElement targetConstraint(JsonObject task) {
        try {
            return replayContract(task).requiredSatisfiedPredicate();
        } catch (IOException malformed) {
            return null;
        }
    }

    private static BranchReplayContract replayContract(JsonObject task)
            throws IOException {
        JsonElement encoded = task == null ? null
                : task.get("replayContract");
        if (encoded == null || !encoded.isJsonObject()) {
            throw new IOException(
                    "canonical path task requires replayContract");
        }
        try {
            return BranchReplayContract.fromJson(encoded.getAsJsonObject());
        } catch (IllegalArgumentException malformed) {
            throw new IOException("invalid branch replay contract: "
                    + malformed.getMessage(), malformed);
        }
    }

    private static void rejectRetiredReplayAliases(JsonObject task)
            throws IOException {
        String[] retired = new String[]{"constraints", "prefix",
                "negatedCondition", "flipSite", "flipOccurrence",
                "conditionIndex", "desiredOutcome",
                "expectedBranchPrefix", "pathReplayConstraints",
                "pathReplayNegatedCondition",
                "pathReplayTargetConditionIndex"};
        for (String field : retired) {
            if (task != null && task.has(field)) {
                throw new IOException("canonical path task rejects retired "
                        + "branch field: " + field);
            }
        }
    }

    private static Set<String> symbolicNames(JsonElement expression) {
        Set<String> result = new LinkedHashSet<>();
        collectSymbolicNames(expression, result);
        return result;
    }

    private static void collectSymbolicNames(JsonElement expression,
                                             Set<String> result) {
        if (expression == null || expression.isJsonNull()) return;
        if (expression.isJsonArray()) {
            for (JsonElement item : expression.getAsJsonArray()) {
                collectSymbolicNames(item, result);
            }
            return;
        }
        if (!expression.isJsonObject()) return;
        JsonObject object = expression.getAsJsonObject();
        String type = string(object, "_type");
        if ("SymbolExpression".equals(type)
                || "ConSymbolExp".equals(type)) {
            String raw = string(object, "_exp");
            if (!raw.isEmpty()) result.add(raw);
            return;
        }
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            collectSymbolicNames(entry.getValue(), result);
        }
    }

    private static ActionMatch bestAction(String raw,
                                          List<JsonObject> actions) {
        ActionMatch best = null;
        int bestLength = -1;
        String normalizedRaw = normalized(raw);
        for (JsonObject action : actions) {
            List<ActionMatch> labels = new ArrayList<>();
            String symbol = string(action, "symbol");
            if (!symbol.isEmpty()) {
                labels.add(new ActionMatch(action,
                        Collections.<String>emptyList(), symbol));
            }
            JsonArray singlePath = array(action, "fieldPath");
            if (singlePath.size() > 0) {
                StringBuilder label = new StringBuilder(symbol);
                List<String> segments = new ArrayList<>();
                for (JsonElement segment : singlePath) {
                    if (!segment.isJsonPrimitive()) continue;
                    String value = segment.getAsString();
                    segments.add(value);
                    label.append('.').append(value);
                }
                labels.add(new ActionMatch(action, segments,
                        label.toString()));
            }
            for (JsonElement path : array(action, "fieldPaths")) {
                if (!path.isJsonArray()) continue;
                StringBuilder label = new StringBuilder(symbol);
                List<String> segments = new ArrayList<>();
                for (JsonElement segment : path.getAsJsonArray()) {
                    try {
                        String value = segment.getAsString();
                        label.append('.').append(value);
                        segments.add(value);
                    } catch (RuntimeException ignored) {
                    }
                }
                labels.add(new ActionMatch(action, segments,
                        label.toString()));
            }
            for (ActionMatch label : labels) {
                String normalizedLabel = normalized(label.label);
                if (!label.label.isEmpty() && (raw.contains(label.label)
                        || !normalizedLabel.isEmpty()
                        && normalizedRaw.contains(normalizedLabel))
                        && normalizedLabel.length() > bestLength) {
                    best = label;
                    bestLength = normalizedLabel.length();
                }
            }
        }
        return best;
    }

    private static MaterializationResolution materializationResolution(
            String raw, MaterializationActionCatalog actions,
            DynamicBindingRegistry registry) {
        DynamicFieldBinding exact = registry.exact(raw);
        if (exact != null) {
            List<JsonObject> exactActions = new ArrayList<>();
            for (JsonObject action : actions.executable) {
                if (exact.baseInputSymbol.equals(string(action, "symbol"))) {
                    exactActions.add(action);
                }
            }
            if (exactActions.isEmpty() && exact.isContainerElement()) {
                for (JsonObject action : actions.declared) {
                    if (exact.matchesSelectorOnlyDeclaration(action)) {
                        exactActions.add(action);
                    }
                }
            }
            if (exactActions.size() != 1) {
                return MaterializationResolution.gap(exactActions.isEmpty()
                        ? "NO_STATIC_ACTION_FOR_DYNAMIC_BASE:"
                        + exact.baseInputSymbol
                        : "AMBIGUOUS_STATIC_ACTION_FOR_DYNAMIC_BASE:"
                        + exact.baseInputSymbol);
            }
            if (exact.isContainerElement()) {
                int containerActions = 0;
                for (JsonObject action : actions.executable) {
                    if (exact.containerInputPort().equals(string(action,
                            "symbol"))
                            && exact.containerInputCell().equals(string(
                            action, "cell"))) {
                        containerActions++;
                    }
                }
                if (containerActions != 1) {
                    return MaterializationResolution.gap(containerActions == 0
                            ? "NO_EXACT_CONTAINER_ACTION_FOR_DYNAMIC_BINDING:"
                            + exact.containerInputPort()
                            : "AMBIGUOUS_CONTAINER_ACTION_FOR_DYNAMIC_BINDING:"
                            + exact.containerInputPort());
                }
            }
            return MaterializationResolution.resolved(new ActionMatch(
                    exactActions.get(0), exact.fieldPath(),
                    exact.baseInputSymbol), exact);
        }

        ActionMatch legacy = bestAction(raw, actions.executable);
        if (legacy == null) {
            return MaterializationResolution.gap(
                    "NO_STATIC_MATERIALIZATION_ACTION");
        }
        String base = string(legacy.action, "symbol");
        List<DynamicFieldBinding> candidates = registry.forBase(base);
        if (!candidates.isEmpty()) {
            if (exactEngineSymbol(raw, base)) {
                return MaterializationResolution.gap(
                        candidates.size() > 1
                                ? "AMBIGUOUS_DYNAMIC_BASE_INPUT:" + base
                                + ":" + candidates.size()
                                : "BASE_ONLY_DYNAMIC_INPUT_PROHIBITED:"
                                + base);
            }
            // Once runtime evidence has split a static field-family input
            // into concrete entry bindings, a model symbol for that family
            // may only select a binding by the binding's complete dynamic
            // symbol.  Falling back through bestAction's substring match
            // would silently attach a prefix collision or malformed VM name
            // to the sole entry in a family.
            return MaterializationResolution.gap(
                    "ENGINE_SYMBOL_NOT_EXACT_DYNAMIC_BINDING:" + raw);
        }
        return MaterializationResolution.resolved(legacy, null);
    }

    private static boolean exactEngineSymbol(String raw, String symbol) {
        if (raw == null || symbol == null || symbol.isEmpty()) return false;
        if (raw.equals(symbol)) return true;
        if (raw.length() <= 10 || raw.charAt(0) != 'M'
                || raw.charAt(1) != '_'
                || "ZCBSIFJDL".indexOf(raw.charAt(2)) < 0
                || !raw.startsWith("_field_", 3)) {
            return false;
        }
        String payload = raw.substring(10);
        if (payload.equals(symbol)) return true;
        String boundary = symbol + "_";
        return payload.startsWith(boundary)
                && legalVmOwnerSuffix(payload.substring(boundary.length()));
    }

    private static boolean legalVmOwnerSuffix(String suffix) {
        return suffix != null && suffix.matches(
                "[A-Za-z_$][A-Za-z0-9_$]*"
                        + "(?:/[A-Za-z_$][A-Za-z0-9_$]*)*");
    }

    private static final class MaterializationActionCatalog {
        private final List<JsonObject> executable;
        private final List<JsonObject> declared;

        private MaterializationActionCatalog(
                List<JsonObject> executable, List<JsonObject> declared) {
            this.executable = executable;
            this.declared = declared;
        }
    }

    private static final class MaterializationResolution {
        private final ActionMatch action;
        private final DynamicFieldBinding binding;
        private final String gap;

        private MaterializationResolution(ActionMatch action,
                                          DynamicFieldBinding binding,
                                          String gap) {
            this.action = action;
            this.binding = binding;
            this.gap = gap == null ? "" : gap;
        }

        private static MaterializationResolution resolved(ActionMatch action,
                                                          DynamicFieldBinding binding) {
            return new MaterializationResolution(action, binding, "");
        }

        private static MaterializationResolution gap(String reason) {
            return new MaterializationResolution(null, null, reason);
        }

        private boolean resolved() {
            return action != null && gap.isEmpty();
        }
    }

    private static final class DynamicBindingRegistry {
        private final List<DynamicFieldBinding> bindings = new ArrayList<>();
        private final Map<String, DynamicFieldBinding> byDynamicSymbol =
                new LinkedHashMap<>();
        private final Map<String, List<DynamicFieldBinding>> byBase =
                new LinkedHashMap<>();
        private final Set<String> problems = new LinkedHashSet<>();

        private static DynamicBindingRegistry from(JsonObject summary) {
            DynamicBindingRegistry result = new DynamicBindingRegistry();
            JsonArray rows = array(summary, "dynamicFieldBindings");
            Set<String> ids = new LinkedHashSet<>();
            Set<String> siteOccurrences = new LinkedHashSet<>();
            for (int index = 0; index < rows.size(); index++) {
                JsonElement element = rows.get(index);
                if (!element.isJsonObject()) {
                    result.problems.add("BINDING_" + index
                            + ":NOT_AN_OBJECT");
                    continue;
                }
                DynamicFieldBinding binding = new DynamicFieldBinding(
                        element.getAsJsonObject());
                List<String> validation = binding.validate();
                for (String problem : validation) {
                    result.problems.add("BINDING_" + index + ":"
                            + problem);
                }
                if (!validation.isEmpty()) continue;
                if (!ids.add(binding.dynamicBindingId)) {
                    result.problems.add("DUPLICATE_DYNAMIC_BINDING_ID:"
                            + binding.dynamicBindingId);
                }
                if (result.byDynamicSymbol.put(binding.dynamicFieldSymbol,
                        binding) != null) {
                    result.problems.add("DUPLICATE_DYNAMIC_FIELD_SYMBOL:"
                            + binding.dynamicFieldSymbol);
                }
                String siteOccurrence = binding.baseInputSymbol + "\n"
                        + binding.materializationSiteId + "\n"
                        + binding.materializationOccurrence;
                if (!siteOccurrences.add(siteOccurrence)) {
                    result.problems.add("DUPLICATE_DYNAMIC_SITE_OCCURRENCE:"
                            + binding.materializationSiteId + "#"
                            + binding.materializationOccurrence);
                }
                result.bindings.add(binding);
                List<DynamicFieldBinding> family = result.byBase.get(
                        binding.baseInputSymbol);
                if (family == null) {
                    family = new ArrayList<>();
                    result.byBase.put(binding.baseInputSymbol, family);
                }
                family.add(binding);
            }
            return result;
        }

        private DynamicFieldBinding exact(String raw) {
            DynamicFieldBinding direct = byDynamicSymbol.get(raw);
            if (direct != null) return direct;
            DynamicFieldBinding selected = null;
            for (DynamicFieldBinding binding : bindings) {
                if (!exactEngineSymbol(raw, binding.dynamicFieldSymbol)) {
                    continue;
                }
                if (selected != null) return null;
                selected = binding;
            }
            return selected;
        }

        private List<DynamicFieldBinding> forBase(String base) {
            List<DynamicFieldBinding> values = byBase.get(base);
            return values == null
                    ? Collections.<DynamicFieldBinding>emptyList() : values;
        }
    }

    private static final class DynamicFieldBinding {
        private static final String MAP_KIND =
                "DYNAMIC_MAP_ENTRY_FIELD_BINDING";
        private static final String CONTAINER_KIND =
                "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING";
        private static final String MAP_AUTHORITY =
                "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                        + "FIELD_SITE_OCCURRENCE";
        private static final String CONTAINER_AUTHORITY =
                "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_AND_"
                        + "STABLE_FIELD_SITE_OCCURRENCE";
        /**
         * A map-entry field model is rebound in the replay JVM by the exact
         * static field-family port, getter site and dynamic occurrence.  The
         * seed entry key is deliberately not a replay selector: map keys may
         * be freshly generated between executions.  Runtime must capture the
         * replay entry's key and the replay validator must join that fresh
         * selector back to the applied assignment before admitting a summary.
         */
        private static final String FRESH_MAP_ENTRY_REBINDING_AUTHORITY =
                "EXACT_BASE_PORT_GETTER_SITE_OCCURRENCE_THEN_"
                        + "FRESH_ENTRY_REBIND_V1";
        private static final String CONTAINER_REPLAY_REBINDING_AUTHORITY =
                "EXACT_STATIC_ARRAY_SELECTOR_THEN_ACTIVATION_LOCAL_"
                        + "IDENTITY_REBIND_V1";
        private final JsonObject raw;
        private final String dynamicBindingId;
        private final String baseInputSymbol;
        private final String dynamicFieldSymbol;
        private final String materializationSiteId;
        private final int materializationOccurrence;

        private DynamicFieldBinding(JsonObject raw) {
            this.raw = raw.deepCopy();
            dynamicBindingId = string(raw, "dynamicBindingId");
            baseInputSymbol = string(raw, "baseInputSymbol");
            dynamicFieldSymbol = string(raw, "dynamicFieldSymbol");
            materializationSiteId = string(raw,
                    "materializationSiteId");
            materializationOccurrence = integer(raw,
                    "materializationOccurrence", -1);
        }

        private List<String> validate() {
            List<String> result = new ArrayList<>();
            String kind = string(raw, "kind");
            boolean map = MAP_KIND.equals(kind);
            boolean container = CONTAINER_KIND.equals(kind);
            if (!map && !container) {
                result.add("WRONG_KIND");
            }
            int expectedSchema = container ? 2 : 1;
            if (integer(raw, "schemaVersion", -1) != expectedSchema) {
                result.add("UNSUPPORTED_SCHEMA_VERSION");
            }
            String expectedAuthority = container ? CONTAINER_AUTHORITY
                    : MAP_AUTHORITY;
            if (!expectedAuthority.equals(string(raw, "authority"))) {
                result.add("WRONG_AUTHORITY");
            }
            if (!bool(raw, "complete", false)) {
                result.add("NOT_COMPLETE");
            }
            if (baseInputSymbol.isEmpty()) result.add("MISSING_BASE_INPUT");
            if (dynamicFieldSymbol.isEmpty()) {
                result.add("MISSING_DYNAMIC_SYMBOL");
            }
            if (materializationSiteId.isEmpty()) {
                result.add("MISSING_MATERIALIZATION_SITE");
            }
            if (materializationOccurrence < 1) {
                result.add("INVALID_MATERIALIZATION_OCCURRENCE");
            }
            if (dynamicBindingId.isEmpty()) {
                result.add("MISSING_DYNAMIC_BINDING_ID");
            }
            if (map) {
                if (raw.get("keyExpression") == null
                        || raw.get("keyExpression").isJsonNull()) {
                    result.add("MISSING_KEY_SELECTOR");
                }
                if (string(raw, "keyExpressionAuthority").isEmpty()) {
                    result.add("MISSING_KEY_SELECTOR_AUTHORITY");
                }
            } else if (container) {
                validateContainerSelector(result);
            }
            if (!dynamicFieldSymbol.isEmpty()
                    && !dynamicBindingId.equals("DYNAMIC_FIELD:"
                    + dynamicFieldSymbol)) {
                result.add("BINDING_ID_SYMBOL_MISMATCH");
            }
            if (!baseInputSymbol.isEmpty()
                    && !materializationSiteId.isEmpty()
                    && materializationOccurrence > 0) {
                String expected = baseInputSymbol + ".field."
                        + sha256(materializationSiteId).substring(0, 12)
                        + ".occ." + materializationOccurrence;
                if (!expected.equals(dynamicFieldSymbol)) {
                    result.add("DYNAMIC_SYMBOL_SITE_OCCURRENCE_MISMATCH");
                }
            }
            return result;
        }

        private void validateContainerSelector(List<String> result) {
            JsonObject selector = object(raw, "containerSelector");
            if (selector.size() == 0) {
                result.add("MISSING_CONTAINER_SELECTOR");
                return;
            }
            String bindingId = string(selector, "bindingId");
            String containerPort = string(selector, "containerInputPort");
            String containerCell = string(selector, "containerInputCell");
            int index = integer(selector, "elementIndex", -1);
            int occurrence = integer(selector, "elementOccurrence", -1);
            if (!"ARRAY_INDEX".equals(string(selector, "kind"))) {
                result.add("WRONG_CONTAINER_SELECTOR_KIND");
            }
            if (!bool(selector, "complete", false)) {
                result.add("INCOMPLETE_CONTAINER_SELECTOR");
            }
            if (bindingId.isEmpty()) {
                result.add("MISSING_CONTAINER_BINDING_ID");
            }
            if (containerPort.isEmpty() || containerCell.isEmpty()) {
                result.add("MISSING_CONTAINER_ENDPOINT");
            }
            if (containerPort.equals(baseInputSymbol)) {
                result.add("CONTAINER_PORT_EQUALS_BASE_INPUT");
            }
            if (!"EXACT_ARRAY_INDEX".equals(string(selector,
                    "selectorAuthority"))) {
                result.add("NON_EXACT_CONTAINER_SELECTOR");
            }
            if (index < 0) result.add("INVALID_CONTAINER_ELEMENT_INDEX");
            if (occurrence < 1
                    || occurrence != materializationOccurrence) {
                result.add("CONTAINER_OCCURRENCE_MISMATCH");
            }
            if (string(selector, "declaredFieldOwnerClass").isEmpty()) {
                result.add("MISSING_DECLARED_FIELD_OWNER");
            }
            if (string(selector, "declaredFieldType").isEmpty()) {
                result.add("MISSING_DECLARED_FIELD_TYPE");
            }
            if (longInteger(selector, "containerObjectToken", 0L) <= 0L
                    || longInteger(selector,
                    "elementObjectToken", 0L) <= 0L) {
                result.add("INVALID_CONTAINER_OBJECT_TOKEN");
            }
            String tokenScope = string(selector, "objectTokenScope");
            if (!"ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                    string(selector, "objectTokenAuthority"))
                    || tokenScope.isEmpty()
                    || !firstNonBlank(string(raw, "objectTokenScope"),
                    tokenScope).equals(tokenScope)
                    || !firstNonBlank(string(raw, "objectTokenAuthority"),
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN")
                    .equals(string(selector, "objectTokenAuthority"))) {
                result.add("INVALID_CONTAINER_OBJECT_TOKEN_SCOPE");
            }
            String resolved = string(selector,
                    "resolvedFromSelectorAuthority");
            if (!("EXACT_ARRAY_INDEX".equals(resolved)
                    || "DISCOVER_UNIQUE_IDENTITY_INDEX".equals(resolved))) {
                result.add("INVALID_CONTAINER_RESOLUTION_AUTHORITY");
            }
            if (!"EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_ACTIVATION_"
                    .concat("LOCAL_ELEMENT_IDENTITY").equals(string(
                            selector, "authority"))) {
                result.add("INVALID_CONTAINER_SELECTOR_AUTHORITY");
            }
        }

        private boolean isContainerElement() {
            return CONTAINER_KIND.equals(string(raw, "kind"));
        }

        /**
         * Selector-only snapshot leaves are declarations, not ordinary
         * executable field hooks.  They may bridge the solver model back to
         * replay only when the declared action exactly matches the imported
         * runtime binding's static field site and full path.
         */
        private boolean matchesSelectorOnlyDeclaration(JsonObject action) {
            if (!isContainerElement()
                    || !baseInputSymbol.equals(string(action, "symbol"))
                    || !"FIELD_ACCESS".equals(string(action,
                    "bindingMode"))
                    || !"HEAP_OBJECT_FIELD".equals(string(action,
                    "location"))
                    || !"STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1"
                    .equals(string(action, "fieldPathAuthority"))
                    || !materializationSiteId.equals(string(action,
                    "accessSiteId"))) {
                return false;
            }
            String signature = string(raw, "fieldSignature");
            List<String> expectedPath = fieldPath();
            List<String> actionPath = new ArrayList<>();
            for (JsonElement segment : array(action, "fieldPath")) {
                if (!segment.isJsonPrimitive()
                        || !segment.getAsJsonPrimitive().isString()
                        || segment.getAsString().isEmpty()) {
                    return false;
                }
                actionPath.add(segment.getAsString());
            }
            JsonObject selector = object(raw, "containerSelector");
            return !signature.isEmpty()
                    && expectedPath.size() >= 2
                    && expectedPath.size() <= 4
                    && expectedPath.equals(actionPath)
                    && signature.equals(string(action, "field"))
                    && signature.equals(string(action,
                    "leafFieldSignature"))
                    && string(selector, "declaredFieldOwnerClass").equals(
                    string(action, "leafOwnerClass"))
                    && expectedPath.get(expectedPath.size() - 1).equals(
                    string(action, "leafField"));
        }

        private String containerInputPort() {
            return string(object(raw, "containerSelector"),
                    "containerInputPort");
        }

        private String containerInputCell() {
            return string(object(raw, "containerSelector"),
                    "containerInputCell");
        }

        private List<String> fieldPath() {
            List<String> result = new ArrayList<>();
            for (JsonElement segment : array(raw, "fieldPath")) {
                try {
                    if (segment.isJsonPrimitive()) {
                        result.add(segment.getAsString());
                    }
                } catch (RuntimeException ignored) {
                }
            }
            return result;
        }

        private void copySelectorTo(JsonObject assignment) {
            assignment.addProperty("dynamicBindingId", dynamicBindingId);
            assignment.addProperty("baseInputSymbol", baseInputSymbol);
            assignment.addProperty("dynamicFieldSymbol",
                    dynamicFieldSymbol);
            assignment.addProperty("materializationSiteId",
                    materializationSiteId);
            assignment.addProperty("materializationOccurrence",
                    materializationOccurrence);
            copy(raw, assignment, "fieldSignature");
            copy(raw, assignment, "fieldPath");
            assignment.addProperty("dynamicFieldBindingKind",
                    string(raw, "kind"));
            JsonObject selector = new JsonObject();
            selector.addProperty("materializationSiteId",
                    materializationSiteId);
            selector.addProperty("materializationOccurrence",
                    materializationOccurrence);
            if (isContainerElement()) {
                JsonObject runtime = object(raw, "containerSelector");
                JsonObject container = new JsonObject();
                for (String member : new String[]{"kind", "bindingId",
                        "containerInputPort", "containerInputCell",
                        "selectorAuthority", "elementIndex",
                        "elementOccurrence", "declaredFieldOwnerClass",
                        "declaredFieldType"}) {
                    copy(runtime, container, member);
                }
                assignment.add("containerSelector", container.deepCopy());
                selector.add("containerSelector", container);
                assignment.addProperty("containerReplayRebindingAuthority",
                        CONTAINER_REPLAY_REBINDING_AUTHORITY);
                assignment.addProperty(
                        "sourceContainerObjectTokensRetained", false);
                for (String member : new String[]{"containerBindingId",
                        "containerInputPort", "containerInputCell",
                        "selectorAuthority", "elementIndex",
                        "elementOccurrence", "declaredFieldOwnerClass",
                        "declaredFieldType"}) {
                    copy(raw, assignment, member);
                }
            } else {
                // Never put a seed-JVM entry id or concrete key into the
                // replay plan.  They identify an activation-local observation,
                // not a stable program input.  The exact occurrence selector
                // below chooses the materialization point; runtime records the
                // fresh entry selector after applying the model.
                assignment.addProperty("dynamicReplayRebindingAuthority",
                        FRESH_MAP_ENTRY_REBINDING_AUTHORITY);
                assignment.addProperty("sourceEntrySelectorRetained", false);
                selector.addProperty("replayRebindingAuthority",
                        FRESH_MAP_ENTRY_REBINDING_AUTHORITY);
                selector.addProperty("sourceEntrySelectorRetained", false);
            }
            assignment.add("dynamicSelector", selector);
        }

        private static void copy(JsonObject from, JsonObject to,
                                 String name) {
            JsonElement value = from.get(name);
            if (value != null) to.add(name, value.deepCopy());
        }
    }

    private static final class ActionMatch {
        private final JsonObject action;
        private final List<String> path;
        private final String label;

        private ActionMatch(JsonObject action, List<String> path,
                            String label) {
            this.action = action;
            this.path = new ArrayList<>(path);
            this.label = label;
        }
    }

    private static Set<String> unmapped(Set<String> expected,
                                        JsonArray assignments) {
        Set<String> mapped = new LinkedHashSet<>();
        for (JsonElement element : assignments) {
            if (element.isJsonObject()) mapped.add(string(
                    element.getAsJsonObject(), "engineSymbol"));
        }
        Set<String> result = new LinkedHashSet<>(expected);
        result.removeAll(mapped);
        return result;
    }

    private static SolverOutput run(Path executable, String input,
                                    long timeoutMillis)
            throws IOException, InterruptedException {
        ProcessBuilder builder = new ProcessBuilder(executable.toString(),
                "-in", "-smt2");
        Process process = builder.start();
        try (OutputStream stream = process.getOutputStream()) {
            stream.write(input.getBytes(StandardCharsets.UTF_8));
        }
        boolean finished = process.waitFor(timeoutMillis,
                TimeUnit.MILLISECONDS);
        if (!finished) {
            process.destroyForcibly();
            process.waitFor();
        }
        String stdout = readAll(process.getInputStream());
        String stderr = readAll(process.getErrorStream());
        return new SolverOutput(finished ? process.exitValue() : -1,
                !finished, stdout, stderr);
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

    private static final class SolverOutput {
        private final int exitCode;
        private final boolean timedOut;
        private final String stdout;
        private final String stderr;

        private SolverOutput(int exitCode, boolean timedOut, String stdout,
                             String stderr) {
            this.exitCode = exitCode;
            this.timedOut = timedOut;
            this.stdout = stdout;
            this.stderr = stderr;
        }
    }

    private static Map<String, String> parseGetValues(String output) {
        Map<String, String> result = new LinkedHashMap<>();
        int newline = output.indexOf('\n');
        if (newline < 0) return result;
        String values = output.substring(newline + 1).trim();
        if (values.isEmpty() || values.startsWith("(")) {
            List<SExpr> expressions = SExpr.parseMany(values);
            for (SExpr root : expressions) collectValuePairs(root, result);
        }
        return result;
    }

    private static void collectValuePairs(SExpr expression,
                                          Map<String, String> result) {
        if (expression.children.size() == 2
                && expression.children.get(0).children.isEmpty()) {
            String name = expression.children.get(0).atom;
            if (name.startsWith("sym__")) {
                result.put(name, expression.children.get(1).render());
                return;
            }
        }
        for (SExpr child : expression.children) collectValuePairs(child,
                result);
    }

    private static final class SExpr {
        private final String atom;
        private final List<SExpr> children;

        private SExpr(String atom, List<SExpr> children) {
            this.atom = atom;
            this.children = children;
        }

        private String render() {
            if (children.isEmpty()) return atom;
            StringBuilder result = new StringBuilder("(");
            for (int index = 0; index < children.size(); index++) {
                if (index > 0) result.append(' ');
                result.append(children.get(index).render());
            }
            return result.append(')').toString();
        }

        private static List<SExpr> parseMany(String value) {
            Parser parser = new Parser(value);
            List<SExpr> result = new ArrayList<>();
            while (parser.hasNext()) {
                SExpr expression = parser.parse();
                if (expression == null) break;
                result.add(expression);
            }
            return result;
        }
    }

    private static final class Parser {
        private final String value;
        private int index;

        private Parser(String value) {
            this.value = value == null ? "" : value;
        }

        private boolean hasNext() {
            skip();
            return index < value.length();
        }

        private SExpr parse() {
            skip();
            if (index >= value.length()) return null;
            if (value.charAt(index) == '(') {
                index++;
                List<SExpr> children = new ArrayList<>();
                while (true) {
                    skip();
                    if (index >= value.length()) break;
                    if (value.charAt(index) == ')') {
                        index++;
                        break;
                    }
                    SExpr child = parse();
                    if (child == null) break;
                    children.add(child);
                }
                return new SExpr("", children);
            }
            StringBuilder atom = new StringBuilder();
            boolean quoted = false;
            while (index < value.length()) {
                char current = value.charAt(index);
                if (current == '"') {
                    quoted = !quoted;
                    atom.append(current);
                    index++;
                    continue;
                }
                if (!quoted && (Character.isWhitespace(current)
                        || current == '(' || current == ')')) break;
                atom.append(current);
                index++;
            }
            return new SExpr(atom.toString(), Collections.<SExpr>emptyList());
        }

        private void skip() {
            while (index < value.length()
                    && Character.isWhitespace(value.charAt(index))) index++;
        }
    }

    private static JsonObject baseRecord(JsonObject task) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "REGION_PATH_EXPLORATION_RECORD");
        result.addProperty("queryKey", string(task, "queryKey"));
        result.addProperty("regionId", string(task, "regionId"));
        result.addProperty("sourceSummaryId", string(task,
                "sourceSummaryId"));
        result.addProperty("sourcePathKey", string(task, "sourcePathKey"));
        try {
            result.addProperty("branchReplayContractId",
                    replayContract(task).contractId());
        } catch (IOException malformed) {
            result.addProperty("branchReplayContractMalformed", true);
        }
        return result;
    }

    private static boolean regionInput(String raw) {
        return raw != null && raw.matches(
                ".*REGION(?:[._-][A-Za-z0-9-]+)+[._-]in[._-][0-9]+.*");
    }

    private static Sort sortOfJava(String javaType) {
        String value = javaType == null ? "" : javaType;
        if ("Z".equals(value) || "boolean".equals(value)) return Sort.BOOL;
        if ("B".equals(value) || "C".equals(value) || "S".equals(value)
                || "I".equals(value) || "J".equals(value)
                || "byte".equals(value) || "char".equals(value)
                || "short".equals(value) || "int".equals(value)
                || "long".equals(value)) return Sort.INT;
        if ("F".equals(value) || "float".equals(value)
                || "java/lang/Float".equals(value)
                || "java.lang.Float".equals(value)) return Sort.FLOAT32;
        if ("D".equals(value) || "double".equals(value)
                || "java/lang/Double".equals(value)
                || "java.lang.Double".equals(value)) return Sort.FLOAT64;
        // Only java.lang.String has the SMT String/content semantics.  A
        // user class whose name happens to contain "String" (for example
        // StringHolder or StringBuilder) is an ordinary reference and may be
        // modeled here only through exact reference/null equality.
        if ("java.lang.String".equals(value)
                || "java/lang/String".equals(value)
                || "Ljava/lang/String;".equals(value)) return Sort.STRING;
        if (value.startsWith("L") || value.startsWith("[")
                || value.contains("/") || value.contains(".")) {
            return Sort.REF;
        }
        return Sort.UNKNOWN;
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
        if ("Z".equals(descriptor)) return Sort.BOOL;
        if ("B".equals(descriptor) || "C".equals(descriptor)
                || "S".equals(descriptor) || "I".equals(descriptor)
                || "J".equals(descriptor)) return Sort.INT;
        if ("F".equals(descriptor)) return Sort.FLOAT32;
        if ("D".equals(descriptor)) return Sort.FLOAT64;
        return descriptor.startsWith("L") || descriptor.startsWith("[")
                ? Sort.REF : Sort.UNKNOWN;
    }

    private static String castDescriptor(String javaType) {
        return JavaPrimitiveSmtSemantics.primitiveDescriptor(javaType);
    }

    /** The VM uses bare L for primitive long conversions, while other IR
     * nodes also use it as a legacy reference tag.  The primitive source
     * disambiguates conversion bytecodes without mistyping a reference cast. */
    private static String castTargetDescriptor(String javaType,
                                               String sourceType) {
        return JavaPrimitiveSmtSemantics.primitiveTargetDescriptor(
                javaType, sourceType);
    }

    private static FloatingKind floatingKind(Sort sort) {
        if (sort == Sort.FLOAT32) return FloatingKind.JAVA_FLOAT;
        if (sort == Sort.FLOAT64) return FloatingKind.JAVA_DOUBLE;
        return FloatingKind.NONE;
    }

    private static String expressionJavaType(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return "";
        JsonObject object = expression.getAsJsonObject();
        String type = string(object, "_type");
        if ("TypeCastExpression".equals(type)) {
            return string(object, "_java_type");
        }
        if ("MethodExpression".equals(type)) {
            return string(object(object, "_res_exp"), "_java_type");
        }
        return string(object, "_java_type");
    }

    private static String constantPayload(String raw) {
        if (raw == null) return "0";
        int first = raw.indexOf('_');
        int second = first < 0 ? -1 : raw.indexOf('_', first + 1);
        return second < 0 ? raw : raw.substring(second + 1);
    }

    private static String integerLiteral(String value) {
        String raw = firstNonBlank(value).trim();
        if (raw.isEmpty() || raw.length() > 1024) return null;
        try {
            BigInteger parsed = new BigInteger(raw);
            return parsed.signum() < 0
                    ? "(- " + parsed.negate().toString() + ")"
                    : parsed.toString();
        } catch (NumberFormatException ignored) {
            return null;
        }
    }

    private static String realLiteral(String value) {
        String raw = firstNonBlank(value).trim();
        if (raw.isEmpty() || raw.length() > 1024
                || "nan".equalsIgnoreCase(raw)
                || "inf".equalsIgnoreCase(raw)
                || "+inf".equalsIgnoreCase(raw)
                || "-inf".equalsIgnoreCase(raw)
                || "infinity".equalsIgnoreCase(raw)
                || "+infinity".equalsIgnoreCase(raw)
                || "-infinity".equalsIgnoreCase(raw)) {
            return null;
        }
        try {
            BigDecimal parsed = new BigDecimal(raw);
            if (Math.abs((long) parsed.scale()) > 1024L
                    || parsed.precision() > 1024) return null;
            String plain = parsed.abs().toPlainString();
            return parsed.signum() < 0 ? "(- " + plain + ")" : plain;
        } catch (NumberFormatException ignored) {
            return null;
        }
    }

    private static String normalizeModelValue(String value) {
        return SmtModelValueCodec.normalizeScalar(value);
    }

    private static String quote(String value) {
        return "\"" + (value == null ? "" : value)
                .replace("\"", "\"\"") + "\"";
    }

    private static String signature(String method, List<Term> arguments,
                                    Sort result) {
        StringBuilder value = new StringBuilder(method).append("->")
                .append(result);
        for (Term argument : arguments) value.append(':').append(argument.sort);
        return value.toString();
    }

    private static String safeName(String value) {
        String safe = value == null ? "" : value.replaceAll(
                "[^A-Za-z0-9_]", "_");
        if (safe.isEmpty()) safe = "empty";
        if (Character.isDigit(safe.charAt(0))) safe = "n_" + safe;
        return safe.length() > 80 ? safe.substring(0, 80) : safe;
    }

    private static String normalized(String value) {
        return value == null ? "" : value.replaceAll("[^A-Za-z0-9]", "")
                .toLowerCase();
    }

    private static String sha256(String value) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] bytes = digest.digest((value == null ? "" : value)
                    .getBytes(StandardCharsets.UTF_8));
            StringBuilder result = new StringBuilder();
            for (byte current : bytes) {
                result.append(String.format("%02x", current & 0xff));
            }
            return result.toString();
        } catch (NoSuchAlgorithmException exception) {
            throw new IllegalStateException(exception);
        }
    }

    private static String firstLine(String value) {
        if (value == null) return "";
        int newline = value.indexOf('\n');
        return (newline < 0 ? value : value.substring(0, newline)).trim();
    }

    private static JsonObject object(JsonObject parent, String name) {
        if (parent == null) return new JsonObject();
        JsonElement value = parent.get(name);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static JsonArray array(JsonObject parent, String name) {
        if (parent == null) return new JsonArray();
        JsonElement value = parent.get(name);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static List<String> stringList(JsonArray values) {
        List<String> result = new ArrayList<>();
        for (JsonElement value : values) {
            try {
                if (value.isJsonPrimitive()
                        && value.getAsJsonPrimitive().isString()
                        && !value.getAsString().isEmpty()) {
                    result.add(value.getAsString());
                }
            } catch (RuntimeException ignored) {
                // A malformed path is not usable as replay identity.
            }
        }
        return result;
    }

    private static String string(JsonObject object, String name) {
        if (object == null) return "";
        JsonElement value = object.get(name);
        try {
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static boolean bool(JsonObject object, String name,
                                boolean fallback) {
        if (object == null) return fallback;
        JsonElement value = object.get(name);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static int integer(JsonObject object, String name, int fallback) {
        if (object == null) return fallback;
        JsonElement value = object.get(name);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long longInteger(JsonObject object, String name,
                                    long fallback) {
        if (object == null) return fallback;
        JsonElement value = object.get(name);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsLong();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static String firstNonBlank(String... values) {
        if (values != null) {
            for (String value : values) {
                if (value != null && !value.trim().isEmpty()) {
                    return value.trim();
                }
            }
        }
        return "";
    }
}
