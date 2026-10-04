package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.smt.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import soot.ArrayType;
import soot.Body;
import soot.RefLikeType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.SootField;
import soot.SootFieldRef;
import soot.jimple.ArrayRef;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.GotoStmt;
import soot.jimple.IfStmt;
import soot.jimple.LookupSwitchStmt;
import soot.jimple.TableSwitchStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.Stmt;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.UUID;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Set;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/** Immutable records and Soot decoding of the static backward analysis. */
public final class CausynthStaticFacts {
    private static final Pattern FIELD_OWNER = Pattern.compile("<([^:]+):");
    static final Pattern METHOD_SIGNATURE = Pattern.compile(
            "<([^:]+):\\s+(.+)\\s+([^\\s(]+)\\((.*)\\)>");

    private CausynthStaticFacts() {
    }

    /** The declaring field, not the constant-pool owner it was named via. */
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

    static String declaredFieldName(SootFieldRef reference) {
        SootField field = declaredField(reference);
        return field == null ? reference.name() : field.getName();
    }

    static final class FieldWrite {
        final String method;
        final String field;
        final int unitIndex;
        final String kind;
        final List<String> sources;

        FieldWrite(String method, String field, int unitIndex, String kind,
                   List<String> sources) {
            this.method = method;
            this.field = field;
            this.unitIndex = unitIndex;
            this.kind = kind;
            this.sources = sources;
        }
    }

    static final class Callsite {
        final String method;
        final int unitIndex;
        final String receiver;
        final List<String> actuals;

        Callsite(String method, int unitIndex, String receiver,
                 List<String> actuals) {
            this.method = method;
            this.unitIndex = unitIndex;
            this.receiver = receiver;
            this.actuals = actuals;
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

    /** One exact, index-stable observation of a Soot unit. */
    static final class Fact {
        final Unit unit;
        final String method;
        final int unitIndex;
        final String unitText;
        final List<String> defs;
        final List<String> uses;
        final List<String> fieldDefs;
        final List<String> fieldUses;
        final List<InstanceFieldAccess> instanceFieldDefs;
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
            this.unitText = ownText(unit);
            this.defs = valueStrings(unit.getDefBoxes());
            this.uses = valueStrings(unit.getUseBoxes());
            this.fieldDefs = fieldRefs(unit.getDefBoxes());
            this.fieldUses = fieldRefs(unit.getUseBoxes());
            this.instanceFieldDefs = instanceFieldRefs(unit.getDefBoxes());
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

        /**
         * The unit's own text.  Soot prints a branch with the statement it
         * jumps to ({@code if $r38 != null goto $r39 = virtualinvoke
         * $r38.<..getRouter()>()}), and every text reader here -- the invoke
         * base, the actual arguments -- read that statement's call as the
         * branch's: the guard's operand was the "receiver" and was dropped,
         * so solr-18413's deciding guard {@code targetColl == null} named no
         * operand and no failure target.
         */
        static String ownText(Unit unit) {
            if (unit instanceof IfStmt) {
                return "if " + ((IfStmt) unit).getCondition();
            }
            if (unit instanceof GotoStmt) {
                return "goto";
            }
            if (unit instanceof TableSwitchStmt) {
                return "tableswitch(" + ((TableSwitchStmt) unit).getKey() + ")";
            }
            if (unit instanceof LookupSwitchStmt) {
                return "lookupswitch(" + ((LookupSwitchStmt) unit).getKey()
                        + ")";
            }
            return unit.toString();
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
                    ref.getIndex().toString());
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

        ArrayAccess(String base, String index) {
            this.base = base;
            this.index = index;
        }
    }

    /** The scene's method for a signature, or null. */
    static SootMethod method(String signature) {
        try {
            return Scene.v().getMethod(signature);
        } catch (RuntimeException absent) {
            return null;
        }
    }

    /** Whether a method is the woven program's: its class is an application
     *  class. */
    static boolean applicationMethod(String signature) {
        SootMethod method = method(signature);
        return method != null
                && method.getDeclaringClass().isApplicationClass();
    }

    /** Whether a method's body is the analysed program's: a concrete method
     *  of an application class. */
    static boolean analysedMethod(String signature) {
        SootMethod method = method(signature);
        return method != null && method.isConcrete()
                && method.getDeclaringClass().isApplicationClass();
    }

    /** Whether a field is a constant: static and final. */
    static boolean constantField(String signature) {
        SootField field = signature == null || signature.isEmpty() ? null
                : Scene.v().grabField(signature);
        return field != null && field.isStatic() && field.isFinal();
    }

    /**
     * How the replay versions a field from any store into it (SYMBOL-SCOPE
     * F2):
     * <ul>
     *   <li>{@code VALUE}: an instance field holding an integral value --
     *       boolean, byte, char, short, int or long, or its wrapper, whose
     *       value (or null) is all a reader observes: a box is immutable and
     *       a store puts a new one (solr-18413's {@code
     *       RoutingRule.expireAt} is a {@code Long}).  Float and double stay
     *       out, boxed or not.</li>
     *   <li>{@code REFERENCE}: a field a store re-points holding an
     *       object, an array included, other than a String or a wrapper: a
     *       reader queries or projects the referent the field held when it
     *       read (solr-18406's {@code knownCommits}, a map each commit
     *       replaces).  A static field too: its location is its class's.</li>
     *   <li>{@code CONTAINER}: a field only its construction stores ({@link
     *       #constructionOnly}) holding a map, set, list, queue or deque
     *       ({@code JavaContainerTypes#shape}; an array is none): its
     *       reference never changes, and the container's contents, mutated
     *       in place, are what a reader queries
     *       ({@code BlockTokenSecretManager.allKeys}).  Any other field only
     *       its construction stores is none: there is nothing to re-pair.</li>
     * </ul>
     */
    static SharedFieldFlow.TrackedKind trackedKind(String signature) {
        SootField field = signature == null || signature.isEmpty() ? null
                : Scene.v().grabField(signature);
        if (field == null) return SharedFieldFlow.TrackedKind.NONE;
        Type type = field.getType();
        if (JavaPrimitiveSmtSemantics.domainOfJavaType(type.toString())
                != null) {
            return field.isStatic() ? SharedFieldFlow.TrackedKind.NONE
                    : SharedFieldFlow.TrackedKind.VALUE;
        }
        if (!(type instanceof RefLikeType)
                || UNVERSIONED_REFERENCES.contains(type.toString())) {
            return SharedFieldFlow.TrackedKind.NONE;
        }
        if (!constructionOnly(field)) {
            return SharedFieldFlow.TrackedKind.REFERENCE;
        }
        return !(type instanceof ArrayType) && JavaContainerTypes.shape(
                type.toString()) != JavaContainerTypes.Shape.NONE
                ? SharedFieldFlow.TrackedKind.CONTAINER
                : SharedFieldFlow.TrackedKind.NONE;
    }

    /**
     * Whether only its own class's construction stores a field: final, or
     * final in effect ({@link #storedOnlyAtConstruction}).  Its one writer
     * is its constructor, so the field itself has nothing to re-pair
     * (SYMBOL-SCOPE §5.1): a read of it is no {@code REFERENCE} read (of a
     * container, a {@code CONTAINER} read of its contents), and a store into it
     * is no guarded store (§5.3) -- a concrete store there starts no log,
     * so the field names no owner its readers would project through
     * (hdfs-adhoc-03: {@code FSOutputSummer.sum}, a final DataChecksum
     * stored under a symbolic guard of {@code newStreamForCreate}, made
     * every chunk's CRC symbolic).
     */
    static boolean constructionOnly(String signature) {
        SootField field = signature == null || signature.isEmpty() ? null
                : Scene.v().grabField(signature);
        return field != null && constructionOnly(field);
    }

    private static boolean constructionOnly(SootField field) {
        return field.isFinal() || storedOnlyAtConstruction(field);
    }

    /**
     * Whether a private field is stored only by its own class's
     * constructors -- its initializer included -- so final in effect:
     * Lucene's {@code IndexFileDeleter.refCounts}, a lambda's captured
     * value.  A private field's every store is in its own class (a nested
     * class stores it through that class's accessor), so reading its
     * class's bodies proves it; a class whose bodies are not loaded proves
     * nothing.
     */
    private static boolean storedOnlyAtConstruction(SootField field) {
        if (!field.isPrivate()) return false;
        String constructor = field.isStatic() ? "<clinit>" : "<init>";
        for (SootMethod method : field.getDeclaringClass().getMethods()) {
            if (!method.isConcrete()) continue;
            Body body = activeBody(method);
            if (body == null) return false;
            if (constructor.equals(method.getName())) continue;
            for (Unit unit : body.getUnits()) {
                for (ValueBox box : unit.getDefBoxes()) {
                    if (box.getValue() instanceof FieldRef && field.equals(
                            declaredField(((FieldRef) box.getValue())
                                    .getFieldRef()))) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /** A String or a wrapper is a value, never a referent a reader
     *  queries; float and double are no tracked value. */
    private static final Set<String> UNVERSIONED_REFERENCES =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "java.lang.String", "java.lang.Float",
                    "java.lang.Double")));

    /** Whether a field is static: its location is its class's. */
    static boolean staticField(String signature) {
        SootField field = signature == null || signature.isEmpty() ? null
                : Scene.v().grabField(signature);
        return field != null && field.isStatic();
    }

    /** A retrievable active body, or null: an unloadable body is not a fact. */
    static Body activeBody(SootMethod method) {
        if (method == null || !method.isConcrete()) return null;
        try {
            return method.retrieveActiveBody();
        } catch (RuntimeException unavailable) {
            return null;
        }
    }

    /** The deterministic name UUID artifacts identify a row by. */
    static String nameId(String prefix, String identity) {
        return prefix + UUID.nameUUIDFromBytes(
                identity.getBytes(StandardCharsets.UTF_8));
    }

    /** The first field {@code owner} itself declares that {@code accepts}. */
    static SootField field(SootClass owner, Predicate<SootField> accepts) {
        if (owner == null) return null;
        for (SootField candidate : owner.getFields()) {
            if (accepts.test(candidate)) return candidate;
        }
        return null;
    }

    /** Declaring type of a field signature, or {@code ""}. */
    public static String fieldOwner(String fieldSignature) {
        if (fieldSignature == null) {
            return "";
        }
        Matcher matcher = FIELD_OWNER.matcher(fieldSignature);
        return matcher.find() ? matcher.group(1) : "";
    }

    public static boolean constructor(String method) {
        return method != null && (method.contains(" <init>(")
                || method.contains(" <clinit>("));
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

    private static List<String> splitTopLevelArgs(String args) {
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
