package edu.uva.liftlab.graphchecker.concolic;

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
 * <p>Unknown library calls are encoded as deterministic uninterpreted
 * functions.  Such a SAT result is only a candidate input: the subsequent
 * unforced concrete replay must observe the requested prefix before the path
 * is admitted into a merged region summary.</p>
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
        JsonArray constraints = array(task, "constraints");
        for (int index = 0; index < constraints.size(); index++) {
            encoder.addConstraint(constraints.get(index), "q" + index);
        }
        String smt = encoder.finish();
        JsonObject record = baseRecord(task);
        record.addProperty("solver", "Z3_SMT2");
        record.addProperty("solverInputHash", sha256(smt));
        record.addProperty("uninterpretedFunctionCount",
                encoder.uninterpretedFunctions.size());
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
        Set<String> targetControlledSymbols = new LinkedHashSet<>(
                targetSymbols);
        targetControlledSymbols.retainAll(encoder.controlledSymbols);
        Set<String> unforcedPrefixSymbols = new LinkedHashSet<>(
                encoder.controlledSymbols);
        unforcedPrefixSymbols.removeAll(targetControlledSymbols);
        JsonArray assignments = modelAssignments(encoder, values,
                activation, dynamicBindings, targetControlledSymbols);
        record.add("modelAssignments", assignments.deepCopy());
        record.addProperty("modelAssignmentCount", assignments.size());
        record.addProperty("modelProjectionPolicy",
                "FLIP_CONDITION_DELTA_ONLY_V1");
        record.addProperty("controlledSymbolCount",
                encoder.controlledSymbols.size());
        record.addProperty("targetControlledSymbolCount",
                targetControlledSymbols.size());
        record.addProperty("unforcedPrefixControlledSymbolCount",
                unforcedPrefixSymbols.size());
        record.add("unforcedPrefixControlledSymbols",
                GSON.toJsonTree(unforcedPrefixSymbols));
        record.addProperty("modelUsedOnlyForReplay", true);
        record.addProperty("branchOverrideAllowed", false);
        if (targetControlledSymbols.isEmpty()) {
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason", "NO_REGION_INPUT_SYMBOL_IN_QUERY");
        } else if (assignments.size() < targetControlledSymbols.size()) {
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason",
                    "NOT_ALL_FLIP_INPUT_SYMBOLS_HAVE_MATERIALIZATION_TARGETS");
            record.add("unmappedInputSymbols", GSON.toJsonTree(
                    unmapped(targetControlledSymbols, assignments)));
            Set<String> resolutionGaps = new LinkedHashSet<>();
            for (String raw : unmapped(targetControlledSymbols,
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
        private final List<String> assertions = new ArrayList<>();
        private final Set<String> unsupported = new LinkedHashSet<>();
        private final Set<String> uninterpretedFunctions =
                new LinkedHashSet<>();
        private final Set<String> controlledSymbols = new LinkedHashSet<>();
        private final Set<String> uncontrolledEnvironmentTerms =
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
            if ("ConstExpr".equals(type)) return constant(object, expected);
            if ("PlaceholderExpression".equals(type)) {
                return placeholder(object, origin);
            }
            if ("BinaryExpression".equals(type)) {
                return binary(object, origin);
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
                return term(object.get("_exp"), sortOfJava(string(object,
                        "_java_type")), origin + ":cast");
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
            Sort sort = expected == null ? sortOfJava(string(expression,
                    "_java_type")) : expected;
            if (sort == Sort.UNKNOWN) sort = Sort.REF;
            String name = rawToName.get(raw);
            if (name == null) {
                name = "sym__" + safeName(raw) + "__"
                        + sha256(raw).substring(0, 10);
                rawToName.put(raw, name);
                rawToSort.put(raw, sort);
                declarations.put(name, sort);
                if (regionInput(raw)) controlledSymbols.add(raw);
            }
            return new Term(name, rawToSort.get(raw));
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
            return new Term(name, Sort.INT);
        }

        private Term constant(JsonObject expression, Sort expected) {
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
                return new Term(integerLiteral(payload), Sort.INT);
            }
            if (sort == Sort.REAL) {
                return new Term(realLiteral(payload), Sort.REAL);
            }
            if (sort == Sort.STRING) {
                return new Term(quote(payload), Sort.STRING);
            }
            if ("N".equals(raw)) return new Term("nullRef", Sort.REF);
            String name = "const__" + safeName(raw) + "__"
                    + sha256(raw).substring(0, 8);
            declarations.put(name, Sort.REF);
            return new Term(name, Sort.REF);
        }

        private Term binary(JsonObject expression, String origin) {
            String operator = string(expression, "_op");
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
            if ("==".equals(operator) || "!=".equals(operator)) {
                if (left.sort != right.sort) {
                    unsupported.add(origin + ":SORT_MISMATCH:" + left.sort
                            + ":" + right.sort);
                    return null;
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
                return new Term("(" + comparison + " " + left.text + " "
                        + right.text + ")", Sort.BOOL);
            }
            String arithmetic = arithmetic(operator);
            if (!arithmetic.isEmpty()) {
                if (!numeric(left.sort) || !numeric(right.sort)) {
                    unsupported.add(origin + ":NON_NUMERIC_ARITHMETIC");
                    return null;
                }
                Sort result = left.sort == Sort.REAL || right.sort == Sort.REAL
                        ? Sort.REAL : Sort.INT;
                return new Term("(" + arithmetic + " " + left.text + " "
                        + right.text + ")", result);
            }
            unsupported.add(origin + ":BINARY_OPERATOR:" + operator);
            return null;
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
            for (int index = 0; index < assertions.size(); index++) {
                result.append("(assert (! ").append(assertions.get(index))
                        .append(" :named pc_").append(index).append("))\n");
            }
            result.append("(check-sat)\n");
            List<String> modelNames = new ArrayList<>();
            for (String raw : controlledSymbols) {
                String name = rawToName.get(raw);
                Sort sort = rawToSort.get(raw);
                if (name != null && sort != Sort.REF
                        && !sort.isArray()) modelNames.add(name);
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
        BOOL("Bool"), INT("Int"), REAL("Real"), STRING("String"),
        REF("Ref"), INT_ARRAY("(Array Int Int)"),
        REAL_ARRAY("(Array Int Real)"), BOOL_ARRAY("(Array Int Bool)"),
        STRING_ARRAY("(Array Int String)"), REF_ARRAY("(Array Int Ref)"),
        UNKNOWN("");

        private final String smt;

        Sort(String smt) {
            this.smt = smt;
        }

        private Sort arraySort() {
            if (this == INT) return INT_ARRAY;
            if (this == REAL) return REAL_ARRAY;
            if (this == BOOL) return BOOL_ARRAY;
            if (this == STRING) return STRING_ARRAY;
            if (this == REF) return REF_ARRAY;
            return UNKNOWN;
        }

        private boolean isArray() {
            return name().endsWith("_ARRAY");
        }
    }

    private static final class Term {
        private final String text;
        private final Sort sort;

        private Term(String text, Sort sort) {
            this.text = text;
            this.sort = sort;
        }

        private boolean isZero() {
            return "0".equals(text);
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
            String value = values.get(solverName);
            if (value == null || sort == Sort.REF || sort.isArray()) continue;
            MaterializationResolution resolution =
                    materializationResolution(raw, actions, registry);
            if (!resolution.resolved()) continue;
            ActionMatch match = resolution.action;
            JsonObject assignment = new JsonObject();
            assignment.addProperty("engineSymbol", raw);
            assignment.addProperty("solverSymbol", solverName);
            assignment.addProperty("inputSymbol", string(match.action,
                    "symbol"));
            assignment.addProperty("valueType", sort.name());
            assignment.addProperty("value", normalizeModelValue(value));
            assignment.addProperty("authority", "Z3_PATH_FLIP_MODEL");
            assignment.addProperty("materializeAtRealDefinition", true);
            assignment.add("target", match.action.deepCopy());
            if (!match.path.isEmpty()) {
                assignment.add("materializationPath",
                        GSON.toJsonTree(match.path));
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
        JsonElement explicit = task == null ? null : task.get(
                "negatedCondition");
        if (explicit != null && explicit.isJsonObject()) return explicit;
        JsonArray constraints = array(task, "constraints");
        return constraints.size() == 0 ? null
                : constraints.get(constraints.size() - 1);
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
        result.addProperty("flipSite", string(task, "flipSite"));
        result.addProperty("flipOccurrence", integer(task,
                "flipOccurrence", 1));
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
        if ("F".equals(value) || "D".equals(value)
                || "float".equals(value) || "double".equals(value)) {
            return Sort.REAL;
        }
        if (value.contains("String")) return Sort.STRING;
        if (value.startsWith("L") || value.startsWith("[")
                || value.contains("/") || value.contains(".")) {
            return Sort.REF;
        }
        return Sort.UNKNOWN;
    }

    private static boolean numeric(Sort sort) {
        return sort == Sort.INT || sort == Sort.REAL;
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
        if ("/".equals(operator)) return "div";
        if ("%".equals(operator)) return "mod";
        return "";
    }

    private static String constantPayload(String raw) {
        if (raw == null) return "0";
        int marker = raw.lastIndexOf('_');
        return marker >= 0 && marker + 1 < raw.length()
                ? raw.substring(marker + 1) : raw;
    }

    private static String integerLiteral(String value) {
        try {
            long parsed = Long.parseLong(value);
            return parsed < 0 ? "(- " + Math.abs(parsed) + ")"
                    : String.valueOf(parsed);
        } catch (RuntimeException ignored) {
            return "0";
        }
    }

    private static String realLiteral(String value) {
        try {
            double parsed = Double.parseDouble(value);
            if (Double.isInfinite(parsed) || Double.isNaN(parsed)) return "0.0";
            return parsed < 0 ? "(- " + Math.abs(parsed) + ")"
                    : String.valueOf(parsed);
        } catch (RuntimeException ignored) {
            return "0.0";
        }
    }

    private static String normalizeModelValue(String value) {
        String trimmed = value == null ? "" : value.trim();
        if (trimmed.startsWith("(- ") && trimmed.endsWith(")")) {
            return "-" + trimmed.substring(3, trimmed.length() - 1).trim();
        }
        return trimmed;
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
