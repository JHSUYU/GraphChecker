package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.shallowCopy;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.plan.BranchPredicateAlgebra;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.ActiveRegion;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Whether the VM's own branch event is the decision the workload just took.
 *
 * <p>R3's gate, and the only thing that decides whether a decision row may
 * carry a term.  Two halves of one question: the event envelope's exact
 * ownership -- this thread's context, this region and task, this site and
 * occurrence, this outcome, one matching record, a condition index inside
 * the new suffix -- and the algebra that says the VM's relation IS the
 * Jimple predicate the source branched on.</p>
 *
 * <p>{@link #observedOperatorImpliesBranch} is the one tolerance in the
 * whole class, and it is named and directional: Soot may describe a
 * selected edge as {@code >=} where the asserted VM relation for that
 * concrete edge is the stronger {@code >} or {@code ==}.  Nothing else
 * here admits a difference.</p>
 *
 * <p>A refusal is a row, not a field: {@link #noteRefused} publishes
 * {@code UNATTESTED_ARM} carrying the attestation's own sentence -- the
 * only reader {@link Attestation#error} has -- beside the named outcome of
 * the condition-window read ({@code BranchObservation.windowOutcome}), so
 * a refused VM range and an event that named no condition at all are two
 * facts on the stream instead of one empty window.</p>
 *
 * <p>Needs back from {@link ConcolicRegionRuntime}: {@code parseJson},
 * {@code rootCause}, and {@code SwitchExpectation}, which belongs to the
 * decision it describes.</p>
 */
final class VmBranchAttestation {
    private VmBranchAttestation() {
    }

    private static final Pattern BRANCH_OPERATOR = Pattern.compile(
            "(?:^|\\s)(==|!=|<=|>=|<|>)(?:\\s|$)");

    /**
     * Names one VM branch event this replay could not attest.
     *
     * <p>The refusal used to travel on {@code
     * VmBranchEventAttestation.error}: 24 call sites built a sentence
     * saying exactly what the VM had handed back, and nothing ever read the
     * field.  A refused attestation means the decision row publishes no
     * site predicate, so the arm it states carries no term -- which is what
     * {@code UNATTESTED_ARM} names, and the row is the reader the field
     * never had.</p>
     */
    static void noteRefused(String siteId, int occurrence,
                            Attestation attestation, String windowOutcome) {
        RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.UNATTESTED_ARM,
                edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC,
                safe(siteId) + "#" + occurrence,
                "this decision publishes no site predicate ("
                        + safe(windowOutcome) + "): " + attestation.error);
    }

    /**
     * @param readEvents the caller's own read of the exact event stream, or
     *                   {@code null} to read it here.  A caller that has
     *                   already asked the stream a question about this event
     *                   passes what it read: a second read costs a full
     *                   serialization and decode of every event the thread has
     *                   recorded, and would let the two answers be taken from
     *                   two different observations of it.
     */
    static Attestation attest(
            ConcolicVmBroker api, ActiveRegion active, String siteId,
            String expression, boolean observedOutcome, long eventId,
            int occurrence, PathConditionWindow conditions, int baseline,
            BranchObservation.SwitchExpectation switchExpectation,
            JsonElement readEvents) {
        if (eventId <= 0L) {
            return Attestation.invalid(
                    "marker returned a non-positive event id");
        }
        final JsonElement parsed;
        if (readEvents != null) {
            parsed = readEvents;
        } else {
            try {
                parsed = ConcolicRegionRuntime.parseJson(api.branchEvents());
            } catch (Throwable throwable) {
                return Attestation.invalid(
                        "event stream is not readable: "
                                + ConcolicRegionRuntime.rootCause(throwable));
            }
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

        JsonObject selected = null;
        int matches = 0;
        for (JsonElement candidate : array(envelope, "events")) {
            if (!candidate.isJsonObject()) continue;
            JsonObject event = candidate.getAsJsonObject();
            if (optionalLongInteger(event, "eventId", -1L) == eventId) {
                selected = event;
                matches++;
            }
        }
        if (matches != 1 || selected == null) {
            return Attestation.invalid(
                    "event id " + eventId + " matched " + matches
                            + " records");
        }
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

    private static Attestation attestSwitchConditions(
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
        String selector = "";
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
            String matchedSelector = switchSelectorIfMatches(condition,
                    operator, key);
            if (matchedSelector.isEmpty()) {
                return Attestation.invalid(
                        "switch condition " + offset
                                + " is not selector " + operator + " "
                                + key);
            }
            if (selector.isEmpty()) {
                selector = matchedSelector;
            } else if (!selector.equals(matchedSelector)) {
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

    private static String switchSelectorIfMatches(
            JsonElement condition, String expectedOperator, int expectedKey) {
        if (condition == null || !condition.isJsonObject()) return "";
        JsonObject object = condition.getAsJsonObject();
        if (!"BinaryExpression".equals(optionalString(object, "_type"))
                || !expectedOperator.equals(optionalString(object, "_op"))) {
            return "";
        }
        JsonElement left = object.get("_left");
        JsonElement right = object.get("_right");
        if (left == null || !left.isJsonObject()
                || right == null || !right.isJsonObject()
                || "ConstExpr".equals(optionalString(left.getAsJsonObject(),
                "_type"))) {
            return "";
        }
        JsonObject constant = right.getAsJsonObject();
        if (!"ConstExpr".equals(optionalString(constant, "_type"))) return "";
        Matcher encoded = Pattern.compile("^Y_I_(-?(?:0|[1-9][0-9]*))$")
                .matcher(optionalString(constant, "_exp"));
        if (!encoded.matches()) return "";
        final int key;
        try {
            key = Integer.parseInt(encoded.group(1));
        } catch (NumberFormatException malformed) {
            return "";
        }
        return key == expectedKey ? left.toString() : "";
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
        Matcher matcher = BRANCH_OPERATOR.matcher(safe(expression));
        if (!matcher.find()) {
            return false;
        }
        String declared = matcher.group(1);
        String expected = outcome ? declared
                : BranchPredicateAlgebra.complementOperator(declared);
        String observed = optionalString(object, "_op");
        if (!observedOperatorImpliesBranch(expected, observed,
                safe(expression).matches(".*\\bnull\\b.*"))) {
            return false;
        }
        if (safe(expression).matches(".*\\bnull\\b.*")) {
            return symbolicNull(object.get("_left"))
                    || symbolicNull(object.get("_right"));
        }
        return true;
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
     * Soot may describe one selected Jimple edge as {@code >=}/{@code <=}
     * while the asserted VM relation for that concrete edge is the stronger
     * {@code >}, {@code <}, or {@code ==}.  Admit only that forward
     * implication, then canonicalize the retained condition to the actual
     * Jimple predicate below.  Numeric {@code *cmp*} bytecodes now propagate
     * their symbolic trichotomy result to the consuming branch; this is not a
     * fallback to the removed concrete compare-witness mechanism.
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
        Matcher matcher = BRANCH_OPERATOR.matcher(safe(expression));
        if (!matcher.find()) {
            return condition;
        }
        String expected = outcome ? matcher.group(1)
                : BranchPredicateAlgebra.complementOperator(
                matcher.group(1));
        String observed = optionalString(original, "_op");
        if (!observedOperatorImpliesBranch(expected, observed,
                safe(expression).matches(".*\\bnull\\b.*"))
                || expected.equals(observed)) {
            return condition;
        }
        JsonObject normalized = shallowCopy(original);
        normalized.addProperty("_op", expected);
        return normalized;
    }

    /**
     * One constraint, negated by spelling, or null.
     *
     * <p>The negation of a relational predicate is the same predicate over
     * the same operands with the complementary operator, so nothing is
     * re-evaluated and no second expression is built: the operands are the
     * VM's own nodes.  Null when the constraint carries no relational
     * operator to complement -- the run then states no term rather than one
     * it cannot spell.</p>
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
