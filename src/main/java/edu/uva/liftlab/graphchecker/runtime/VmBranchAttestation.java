package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.plan.BranchPredicateAlgebra;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.shallowCopy;

/**
 * Whether the VM's branch event is the decision the workload just took --
 * the gate, the only thing that lets a decision row carry a term.
 *
 * <p>Two checks: the event's exact ownership (thread context, region, task,
 * site, occurrence, outcome, one record, a condition index in the new
 * suffix), and that the VM relation IS the Jimple predicate.  The one
 * tolerance is {@link #observedOperatorImpliesBranch}.  A refusal is
 * published as an {@code UNATTESTED_ARM} gap by {@link #noteRefused}.</p>
 */
final class VmBranchAttestation {
    private VmBranchAttestation() {
    }

    private static final Pattern BRANCH_OPERATOR = Pattern.compile(
            "(?:^|\\s)(==|!=|<=|>=|<|>)(?:\\s|$)");
    /** The VM's spelling of an int constant, {@code Y_I_<value>}. */
    private static final Pattern INT_CONSTANT =
            Pattern.compile("^Y_I_(-?(?:0|[1-9][0-9]*))$");

    /**
     * Names one VM branch event this replay could not attest: its decision
     * row carries no site predicate, so its arm has no term.
     */
    static void noteRefused(String siteId, int occurrence,
                            Attestation attestation, String windowOutcome) {
        RowRuntime.gap(GapKind.UNATTESTED_ARM, GapClass.DIAGNOSTIC,
                safe(siteId) + "#" + occurrence,
                "this decision publishes no site predicate ("
                        + safe(windowOutcome) + "): " + attestation.error);
    }

    /**
     * @param parsed the caller's read of the event stream: both answers come
     *               from one (costly) observation.
     */
    static Attestation attest(
            ActiveRegion active, String siteId,
            String expression, boolean observedOutcome, long eventId,
            int occurrence, PathConditionWindow conditions, int baseline,
            BranchObservation.SwitchExpectation switchExpectation,
            JsonElement parsed) {
        if (eventId <= 0L) {
            return Attestation.invalid(
                    "marker returned a non-positive event id");
        }
        if (!parsed.isJsonObject()) {
            return Attestation.invalid(
                    "event stream is not a JSON object");
        }
        JsonObject envelope = parsed.getAsJsonObject();
        if (optionalInteger(envelope, "schemaVersion", -1) != 1
                || !"CONCOLIC_THREAD_BRANCH_EVENTS".equals(
                optionalString(envelope, "kind"))
                || !optionalBool(envelope, "active", false)) {
            return Attestation.invalid(
                    "unexpected or inactive event stream");
        }
        long envelopeContext = optionalLongInteger(envelope, "contextId", 0L);
        long envelopeOwner = optionalLongInteger(envelope,
                "ownerJavaThreadId", 0L);
        if (envelopeContext <= 0L) {
            return Attestation.invalid(
                    "missing positive VM thread context id");
        }
        if (envelopeOwner != active.thread.getId()) {
            return Attestation.invalid(
                    "event stream belongs to Java thread " + envelopeOwner
                            + " instead of " + active.thread.getId());
        }
        if (!safe(active.activation.regionId).equals(
                optionalString(envelope, "regionId"))
                || !safe(active.activation.taskId).equals(
                optionalString(envelope, "taskId"))) {
            return Attestation.invalid(
                    "event stream region/task does not match owner");
        }

        List<JsonObject> numbered = PathConditionWindow.eventsNumbered(
                envelope, eventId);
        if (numbered.size() != 1) {
            return Attestation.invalid(
                    "event id " + eventId + " matched " + numbered.size()
                            + " records");
        }
        JsonObject selected = numbered.get(0);
        String authority = optionalString(selected, "authority");
        if (!"VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1".equals(authority)) {
            return Attestation.invalid(
                    "unsupported event authority " + authority);
        }
        if (!safe(siteId).equals(optionalString(selected, "siteId"))
                || optionalInteger(selected, "occurrence", -1) != occurrence) {
            return Attestation.invalid(
                    "event site/occurrence does not match prepared branch");
        }
        if (optionalBool(selected, "outcome", !observedOutcome)
                != observedOutcome) {
            return Attestation.invalid(
                    "event outcome differs from observed branch");
        }
        JsonArray indices = array(selected, "conditionIndices");
        if (optionalInteger(selected, "conditionCount", -1) != indices.size()) {
            return Attestation.invalid(
                    "event condition count differs from its index vector");
        }
        if (switchExpectation != null) {
            return attestSwitchConditions(selected,
                    switchExpectation, indices, conditions);
        }
        if (indices.size() > 1) {
            return Attestation.invalid(
                    "instrumented IfStmt emitted multiple condition indices");
        }
        int conditionIndex = -1;
        if (indices.size() == 1) {
            try {
                conditionIndex = indices.get(0).getAsInt();
            } catch (RuntimeException exception) {
                return Attestation.invalid(
                        "condition index is not an integer");
            }
            if (conditionIndex < baseline
                    || conditionIndex >= conditions.size()) {
                return Attestation.invalid(
                        "condition index " + conditionIndex
                                + " is outside new path-condition suffix ["
                                + baseline + "," + conditions.size() + ")");
            }
            if (!conditionMatches(expression, observedOutcome,
                    conditions.get(conditionIndex))) {
                return Attestation.invalid(
                        "selected VM condition does not match the original "
                                + "branch predicate");
            }
        }
        return Attestation.valid(
                conditionIndex < 0
                        ? Collections.<Integer>emptyList()
                        : Collections.singletonList(conditionIndex));
    }

    static Attestation attestSwitchConditions(
            JsonObject event, BranchObservation.SwitchExpectation expected,
            JsonArray rawIndices, PathConditionWindow conditions) {
        int expectedOpcode = "TABLE_SWITCH".equals(expected.branchKind)
                ? 170 : 171;
        if (optionalInteger(event, "opcode", -1) != expectedOpcode) {
            return Attestation.invalid(
                    "event opcode does not match static "
                            + expected.branchKind);
        }
        if (optionalString(event, "codePosition").isEmpty()) {
            return Attestation.invalid(
                    "switch event has no bytecode position");
        }

        int completeSymbolicCount = expected.caseArm()
                ? 1 : expected.caseKeys.size();
        // The VM still emits an exact event when the selector is concrete.
        if (rawIndices.size() == 0) {
            return Attestation.valid(
                    Collections.<Integer>emptyList());
        }
        if (rawIndices.size() != completeSymbolicCount) {
            return Attestation.invalid(
                    "switch arm owns " + rawIndices.size()
                            + " conditions; exact arm requires "
                            + completeSymbolicCount);
        }
        List<Integer> indices = new ArrayList<>();
        JsonObject selector = null;
        String expectedPosition = optionalString(event, "codePosition");
        int previousIndex = -1;
        for (int offset = 0; offset < rawIndices.size(); offset++) {
            final int conditionIndex;
            try {
                conditionIndex = rawIndices.get(offset).getAsInt();
            } catch (RuntimeException malformed) {
                return Attestation.invalid(
                        "switch condition index is not an integer");
            }
            if (conditionIndex < 0
                    || offset > 0 && conditionIndex != previousIndex + 1) {
                return Attestation.invalid(
                        "switch condition indices are not one exact ordered "
                                + "VM event range");
            }
            final JsonElement condition;
            try {
                condition = conditions.get(conditionIndex);
            } catch (IndexOutOfBoundsException unavailable) {
                return Attestation.invalid(
                        "switch condition index " + conditionIndex
                                + " is outside the exact VM event range");
            }
            int key = expected.caseArm()
                    ? expected.caseKeys.get(
                    expected.observedSuccessorIndex)
                    : expected.caseKeys.get(offset);
            String operator = expected.caseArm() ? "==" : "!=";
            JsonObject matchedSelector = switchSelectorIfMatches(condition,
                    operator, key);
            if (matchedSelector == null) {
                return Attestation.invalid(
                        "switch condition " + offset
                                + " is not selector " + operator + " "
                                + key);
            }
            if (selector == null) {
                selector = matchedSelector;
            } else if (!sameExpression(selector, matchedSelector)) {
                return Attestation.invalid(
                        "switch conditions do not share one selector");
            }
            String conditionPosition = condition.isJsonObject()
                    ? optionalString(condition.getAsJsonObject(), "_code_position")
                    : "";
            if (!conditionPosition.isEmpty()
                    && !expectedPosition.equals(conditionPosition)) {
                return Attestation.invalid(
                        "switch condition bytecode position differs from "
                                + "its exact event");
            }
            indices.add(conditionIndex);
            previousIndex = conditionIndex;
        }
        return Attestation.valid(indices);
    }

    /** The selector of {@code selector <op> key}, or null when the
     *  condition is not that comparison. */
    private static JsonObject switchSelectorIfMatches(
            JsonElement condition, String expectedOperator, int expectedKey) {
        if (condition == null || !condition.isJsonObject()) return null;
        JsonObject object = condition.getAsJsonObject();
        if (!"BinaryExpression".equals(optionalString(object, "_type"))
                || !expectedOperator.equals(optionalString(object, "_op"))) {
            return null;
        }
        JsonElement left = object.get("_left");
        JsonElement right = object.get("_right");
        if (left == null || !left.isJsonObject()
                || right == null || !right.isJsonObject()
                || "ConstExpr".equals(optionalString(left.getAsJsonObject(),
                "_type"))) {
            return null;
        }
        JsonObject constant = right.getAsJsonObject();
        if (!"ConstExpr".equals(optionalString(constant, "_type"))) {
            return null;
        }
        Matcher encoded = INT_CONSTANT.matcher(
                optionalString(constant, "_exp"));
        if (!encoded.matches()) return null;
        final int key;
        try {
            key = Integer.parseInt(encoded.group(1));
        } catch (NumberFormatException malformed) {
            return null;
        }
        return key == expectedKey ? left.getAsJsonObject() : null;
    }

    /**
     * Whether two VM expressions are one: the same node, or equal refs
     * ({@link RowRuntime#refOf}, each node hashed once).  Never their
     * renderings: the decoder shares nodes and a FieldAccessExpression
     * names its owner twice, so a rendering doubles per level -- SOLR-18413's
     * verifyProp selector was 1,060 nodes and 7.4e10 as a tree, and one
     * toString ran over 70 s on the workload's thread.
     */
    static boolean sameExpression(JsonObject left, JsonObject right) {
        return left == right
                || RowRuntime.refOf(left).equals(RowRuntime.refOf(right));
    }

    static boolean conditionMatches(String expression, boolean outcome,
                                    JsonElement condition) {
        if (condition == null || !condition.isJsonObject()) {
            return false;
        }
        JsonObject object = condition.getAsJsonObject();
        if (!"BinaryExpression".equals(optionalString(object, "_type"))) {
            Boolean requiredValue = booleanValueRequiredByZeroBranch(
                    expression, outcome);
            Boolean representedValue = representedBooleanValue(object);
            return requiredValue != null && representedValue != null
                    && requiredValue.equals(representedValue);
        }
        String expected = armOperator(expression, outcome);
        if (expected == null) return false;
        boolean nullComparison = nullComparison(expression);
        if (!observedOperatorImpliesBranch(expected,
                optionalString(object, "_op"), nullComparison)) {
            return false;
        }
        return !nullComparison || symbolicNull(object.get("_left"))
                || symbolicNull(object.get("_right"));
    }

    /**
     * The operator the taken arm asserts: the Jimple one, complemented on
     * the fall-through; null when the expression states none.
     */
    private static String armOperator(String expression, boolean outcome) {
        Matcher matcher = BRANCH_OPERATOR.matcher(safe(expression));
        if (!matcher.find()) return null;
        return outcome ? matcher.group(1)
                : BranchPredicateAlgebra.complementOperator(matcher.group(1));
    }

    private static boolean nullComparison(String expression) {
        return safe(expression).matches(".*\\bnull\\b.*");
    }

    /** Resolves the Java boolean value selected by a Jimple zero test. */
    private static Boolean booleanValueRequiredByZeroBranch(
            String expression, boolean outcome) {
        String rendered = safe(expression).trim();
        Matcher matcher = BRANCH_OPERATOR.matcher(rendered);
        if (!matcher.find()) return null;
        String declared = matcher.group(1);
        if (!("==".equals(declared) || "!=".equals(declared))) {
            return null;
        }
        String left = rendered.substring(0, matcher.start()).trim();
        String right = rendered.substring(matcher.end()).trim();
        boolean leftZero = "0".equals(left);
        boolean rightZero = "0".equals(right);
        if (leftZero == rightZero) return null;
        String effective = outcome ? declared
                : BranchPredicateAlgebra.complementOperator(declared);
        return "!=".equals(effective);
    }

    /**
     * Returns the underlying Java boolean represented by an asserted engine
     * condition, or {@code null} when the IR node is value-producing or its
     * semantics are not part of the exact codec.
     */
    private static Boolean representedBooleanValue(JsonObject condition) {
        if (!"OpStrExpression".equals(optionalString(condition, "_type"))) {
            return null;
        }
        String operation = optionalString(condition, "_name");
        int expectedArity;
        if ("isEmpty".equals(operation)) {
            expectedArity = 1;
        } else if ("contains".equals(operation)
                || "equals".equals(operation)
                || "startsWith".equals(operation)
                || "endsWith".equals(operation)) {
            expectedArity = 2;
        } else {
            return null;
        }
        if (array(condition, "_param_list").size() != expectedArity) {
            return null;
        }
        return !optionalBool(condition, "_is_not", false);
    }

    /**
     * The one tolerance: Soot may spell an edge {@code >=}/{@code <=} where
     * the VM asserts the stronger {@code >}, {@code <} or {@code ==}.  Only
     * that forward implication is admitted; {@link #semanticCondition} then
     * restores the Jimple operator.
     */
    private static boolean observedOperatorImpliesBranch(
            String expected, String observed, boolean nullComparison) {
        if (expected.equals(observed)) {
            return true;
        }
        if (nullComparison) {
            return false;
        }
        return ">=".equals(expected)
                && (">".equals(observed) || "==".equals(observed))
                || "<=".equals(expected)
                && ("<".equals(observed) || "==".equals(observed));
    }

    /** Returns the branch-level predicate while retaining the VM operands. */
    static JsonElement semanticCondition(
            String expression, boolean outcome, JsonElement condition) {
        if (condition == null || !condition.isJsonObject()) {
            return condition;
        }
        JsonObject original = condition.getAsJsonObject();
        if (!"BinaryExpression".equals(optionalString(original, "_type"))) {
            return condition;
        }
        String expected = armOperator(expression, outcome);
        if (expected == null) return condition;
        String observed = optionalString(original, "_op");
        if (expected.equals(observed) || !observedOperatorImpliesBranch(
                expected, observed, nullComparison(expression))) {
            return condition;
        }
        JsonObject normalized = shallowCopy(original);
        normalized.addProperty("_op", expected);
        return normalized;
    }

    /**
     * One constraint negated by complementing its operator over the VM's own
     * operands, or null when it has no relational operator.
     */
    static JsonElement negated(JsonElement condition) {
        if (condition == null || !condition.isJsonObject()) return null;
        JsonObject original = condition.getAsJsonObject();
        String operator = binaryOperator(original);
        if (operator.isEmpty()) return null;
        final String complement;
        try {
            complement = BranchPredicateAlgebra.complementOperator(operator);
        } catch (IllegalArgumentException unsupported) {
            return null;
        }
        JsonObject negated = shallowCopy(original);
        negated.addProperty("_op", complement);
        return negated;
    }

    private static String binaryOperator(JsonElement condition) {
        return condition != null && condition.isJsonObject()
                ? optionalString(condition.getAsJsonObject(), "_op") : "";
    }

    private static boolean symbolicNull(JsonElement element) {
        if (element == null || !element.isJsonObject()) {
            return false;
        }
        JsonObject object = element.getAsJsonObject();
        return "SymbolExpression".equals(optionalString(object, "_type"))
                && VmExpressionIr.SYMBOLIC_NULL.equals(
                optionalString(object, "_exp"));
    }

    static final class Attestation {
        final List<Integer> conditionIndices;
        final boolean valid;
        /** Read by {@link VmBranchAttestation#noteRefused} and nothing else. */
        final String error;

        private Attestation(List<Integer> conditionIndices,
                            boolean valid, String error) {
            this.conditionIndices = Collections.unmodifiableList(
                    new ArrayList<>(conditionIndices));
            this.valid = valid;
            this.error = safe(error);
        }

        private static Attestation valid(
                List<Integer> conditionIndices) {
            return new Attestation(conditionIndices, true, "");
        }

        private static Attestation invalid(String error) {
            return new Attestation(
                    Collections.<Integer>emptyList(), false, error);
        }
    }
}
