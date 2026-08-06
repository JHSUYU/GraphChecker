package edu.uva.liftlab.graphchecker.causynth;

import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.SootField;
import soot.SootFieldRef;
import soot.jimple.ArrayRef;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.Stmt;
import soot.tagkit.LineNumberTag;
import soot.tagkit.SourceLineNumberTag;
import soot.tagkit.Tag;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Immutable records and Soot decoding used by the static backward analysis.
 *
 * <p>This class is deliberately independent of the worklist and graph state:
 * it turns one exact Soot {@link Unit} into a stable {@link Fact}, parses
 * rendered call arguments without losing nested delimiters, and owns the
 * small typed records stored by the analyzer's global indices.  Keeping this
 * bytecode-facing model outside {@link CausynthPipeline} prevents the pipeline
 * orchestration class from also becoming the representation layer.</p>
 */
final class CausynthStaticFacts {
    private static final Pattern FIELD_OWNER = Pattern.compile("<([^:]+):");

    private CausynthStaticFacts() {
    }

    /**
     * Canonical Java field identity is the actual declaring field, not the
     * constant-pool owner through which inherited bytecode happened to refer
     * to it.
     */
    static SootField declaredField(SootFieldRef reference) {
        if (reference == null) return null;
        try {
            return reference.resolve();
        } catch (RuntimeException unresolved) {
            return null;
        }
    }

    static String declaredFieldSignature(SootFieldRef reference) {
        SootField field = declaredField(reference);
        return field == null ? reference.getSignature()
                : field.getSignature();
    }

    static final class FieldWrite {
        final String method;
        final String field;
        final Fact fact;
        final String kind;
        final List<String> sources;
        final String evidence;

        FieldWrite(String method, String field, Fact fact, String kind,
                   List<String> sources, String evidence) {
            this.method = method;
            this.field = field;
            this.fact = fact;
            this.kind = kind;
            this.sources = sources;
            this.evidence = evidence;
        }
    }

    static final class ConstructorCallsite {
        final String method;
        final String constructor;
        final Fact fact;
        final String receiver;
        final List<String> actuals;

        ConstructorCallsite(String method, String constructor, Fact fact,
                            String receiver, List<String> actuals) {
            this.method = method;
            this.constructor = constructor;
            this.fact = fact;
            this.receiver = receiver;
            this.actuals = actuals;
        }
    }

    static final class MethodCallsite {
        final String method;
        final String callee;
        final Fact fact;
        final String receiver;
        final List<String> actuals;
        final List<String> defs;

        MethodCallsite(String method, String callee, Fact fact,
                       String receiver, List<String> actuals,
                       List<String> defs) {
            this.method = method;
            this.callee = callee;
            this.fact = fact;
            this.receiver = receiver;
            this.actuals = actuals;
            this.defs = defs;
        }
    }

    static final class ConstructorParam {
        final String constructor;
        final int index;
        final String formal;

        ConstructorParam(String constructor, int index, String formal) {
            this.constructor = constructor;
            this.index = index;
            this.formal = formal;
        }
    }

    static final class ExceptionGuard {
        final Fact fact;
        final Boolean requiredOutcome;
        final List<Integer> reachingSuccessorIndices;
        final CausynthBranchShape branchShape;

        ExceptionGuard(Fact fact, Boolean requiredOutcome,
                       List<Integer> reachingSuccessorIndices,
                       CausynthBranchShape branchShape) {
            this.fact = fact;
            this.requiredOutcome = requiredOutcome;
            this.reachingSuccessorIndices = reachingSuccessorIndices;
            this.branchShape = branchShape;
        }
    }

    /** One exact, index-stable observation of a Soot unit. */
    static final class Fact {
        final Unit unit;
        final String method;
        final int unitIndex;
        final int line;
        final String unitText;
        final List<String> defs;
        final List<String> uses;
        final List<String> fieldDefs;
        final List<String> fieldUses;
        final List<InstanceFieldAccess> instanceFieldDefs;
        final List<InstanceFieldAccess> instanceFieldUses;
        final ArrayAccess arrayDef;
        final ArrayAccess arrayUse;
        final String invoke;
        final boolean isReturn;
        final boolean isThrow;
        final boolean isBranch;

        Fact(String method, int unitIndex, Unit unit) {
            this.unit = unit;
            this.method = method;
            this.unitIndex = unitIndex;
            this.line = lineOf(unit);
            this.unitText = unit.toString();
            this.defs = valueStrings(unit.getDefBoxes());
            this.uses = valueStrings(unit.getUseBoxes());
            this.fieldDefs = fieldRefs(unit.getDefBoxes());
            this.fieldUses = fieldRefs(unit.getUseBoxes());
            this.instanceFieldDefs = instanceFieldRefs(unit.getDefBoxes());
            this.instanceFieldUses = instanceFieldRefs(unit.getUseBoxes());
            DefinitionStmt definition = unit instanceof DefinitionStmt
                    ? (DefinitionStmt) unit : null;
            this.arrayDef = definition == null
                    ? null : arrayAccess(definition.getLeftOp());
            this.arrayUse = definition == null
                    ? null : arrayAccess(definition.getRightOp());
            this.invoke = invokeSignature(unit);
            String lower = unitText.trim().toLowerCase(Locale.ROOT);
            this.isReturn = lower.startsWith("return");
            this.isThrow = lower.startsWith("throw ");
            this.isBranch = lower.startsWith("if ")
                    || lower.startsWith("tableswitch")
                    || lower.startsWith("lookupswitch");
        }

        private static String invokeSignature(Unit unit) {
            if (unit instanceof Stmt && ((Stmt) unit).containsInvokeExpr()) {
                return ((Stmt) unit).getInvokeExpr().getMethodRef()
                        .getSignature();
            }
            return null;
        }

        private static List<String> fieldRefs(List<ValueBox> boxes) {
            Set<String> fields = new LinkedHashSet<>();
            for (ValueBox box : boxes) {
                Value value = box.getValue();
                if (value instanceof FieldRef) {
                    fields.add(declaredFieldSignature(
                            ((FieldRef) value).getFieldRef()));
                }
            }
            return new ArrayList<>(fields);
        }

        private static List<InstanceFieldAccess> instanceFieldRefs(
                List<ValueBox> boxes) {
            List<InstanceFieldAccess> accesses = new ArrayList<>();
            Set<String> seen = new LinkedHashSet<>();
            for (ValueBox box : boxes) {
                Value value = box.getValue();
                if (value instanceof InstanceFieldRef) {
                    InstanceFieldRef ref = (InstanceFieldRef) value;
                    String base = ref.getBase().toString();
                    String field = declaredFieldSignature(
                            ref.getFieldRef());
                    String key = base + "\n" + field;
                    if (seen.add(key)) {
                        accesses.add(new InstanceFieldAccess(base, field));
                    }
                }
            }
            return accesses;
        }

        private static List<String> valueStrings(List<ValueBox> boxes) {
            List<String> values = new ArrayList<>();
            for (ValueBox box : boxes) {
                values.add(box.getValue().toString());
            }
            return values;
        }

        private static ArrayAccess arrayAccess(Value value) {
            if (!(value instanceof ArrayRef)) {
                return null;
            }
            ArrayRef ref = (ArrayRef) value;
            return new ArrayAccess(ref.getBase().toString(),
                    ref.getIndex().toString(), ref.getType().toString());
        }

        private static int lineOf(Unit unit) {
            for (Tag tag : unit.getTags()) {
                if (tag instanceof SourceLineNumberTag) {
                    return ((SourceLineNumberTag) tag).getStartLineNumber();
                }
                if (tag instanceof LineNumberTag) {
                    return ((LineNumberTag) tag).getLineNumber();
                }
            }
            return unit.getJavaSourceStartLineNumber();
        }
    }

    static final class InstanceFieldAccess {
        final String base;
        final String field;

        InstanceFieldAccess(String base, String field) {
            this.base = base;
            this.field = field;
        }
    }

    /** One top-level Jimple array load or store operand. */
    static final class ArrayAccess {
        final String base;
        final String index;
        final String elementType;

        ArrayAccess(String base, String index, String elementType) {
            this.base = base;
            this.index = index;
            this.elementType = elementType;
        }
    }

    static String fieldOwner(String fieldSignature) {
        if (fieldSignature == null) {
            return "";
        }
        Matcher matcher = FIELD_OWNER.matcher(fieldSignature);
        return matcher.find() ? matcher.group(1) : "";
    }

    static List<String> actualInvokeArgs(String unit) {
        if (unit == null) {
            return Collections.emptyList();
        }
        int start = unit.lastIndexOf(">(");
        int end = unit.lastIndexOf(')');
        if (start < 0 || end <= start + 2) {
            return Collections.emptyList();
        }
        return splitTopLevelArgs(unit.substring(start + 2, end));
    }

    static List<String> splitTopLevelArgs(String args) {
        if (args == null || args.trim().isEmpty()) {
            return Collections.emptyList();
        }
        List<String> values = new ArrayList<>();
        StringBuilder current = new StringBuilder();
        int depth = 0;
        for (int index = 0; index < args.length(); index++) {
            char character = args.charAt(index);
            if (character == '(' || character == '<' || character == '[') {
                depth++;
            } else if (character == ')' || character == '>'
                    || character == ']') {
                depth = Math.max(0, depth - 1);
            }
            if (character == ',' && depth == 0) {
                String value = current.toString().trim();
                if (!value.isEmpty()) {
                    values.add(value);
                }
                current.setLength(0);
            } else {
                current.append(character);
            }
        }
        String value = current.toString().trim();
        if (!value.isEmpty()) {
            values.add(value);
        }
        return values;
    }
}
