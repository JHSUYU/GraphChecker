package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import edu.uva.liftlab.graphchecker.compose.ContainerSmtCodec.Host;
import edu.uva.liftlab.graphchecker.compose.ContainerSmtCodec.Sort;
import edu.uva.liftlab.graphchecker.compose.ContainerSmtCodec.Term;

/**
 * THE CONTAINER STATE MODEL: the sorts a container state is written in, and
 * the one boxing between a Java cell and a {@code Value}.
 *
 * <p>Relocated out of {@link ContainerSmtCodec} unchanged.  Everything here
 * is a statement about the MODEL -- the {@code Value} datatype, the
 * {@code IndexedState}/{@code AssocState} datatypes and the functions over
 * them, which tag a Java value carries, and how a cell is boxed and
 * unboxed.  Nothing here reads a recorded expression: what a particular
 * container operation lowers to is {@link ContainerSmtCodec}'s, and the two
 * were one 2,466-line file in which the model and the walks over it read as
 * one subject.</p>
 */
public final class ContainerStateModel {
    private ContainerStateModel() {
    }

    /**
     * Both operations denote the exact empty container.  They state different
     * provenance, which the caller keeps; the lowering is the same.
     */
    static boolean emptiesState(String operation) {
        return "CLEAR".equals(operation) || "SNAPSHOT_BASE".equals(operation);
    }

    /**
     * Whether this container operation CHANGES the state it stands on.
     *
     * <p>The whole mutating vocabulary {@link ContainerSmtCodec} lowers:
     * {@code WRITE}, {@code APPEND}, {@code INSERT} and {@code REMOVE} on
     * an indexed container, {@code PUT}, {@code REMOVE}, {@code REMOVE_AT}
     * and {@code REMOVE_IF} on an associative one, and {@code CLEAR} on
     * either.  Every other operation the codec names -- {@code STATE},
     * {@code READ}, {@code SIZE}, {@code CONTAINS}, {@code IS_EMPTY}, the
     * views and cursors, and {@code SNAPSHOT_BASE}, which states where a
     * chain was BASED and not a change made to it -- observes and does not
     * mutate.</p>
     */
    static boolean mutates(String operation) {
        return "WRITE".equals(operation) || "APPEND".equals(operation)
                || "INSERT".equals(operation) || "REMOVE".equals(operation)
                || "REMOVE_AT".equals(operation)
                || "REMOVE_IF".equals(operation) || "PUT".equals(operation)
                || "CLEAR".equals(operation);
    }

    /**
     * The cell that holds Java null: one spelling for every caller.
     *
     * <p>It is the value an absent element denotes, the value a refused
     * read leaves behind, and what a {@code null} leaf lowers to where the
     * relation it stands in is written over cells rather than over
     * references.</p>
     */
    public static final String NULL_CELL = "(VRef nullRef)";

    /** One tagged transport value shared by path solving and composition. */
    public static String valueDatatypeDeclaration() {
        return "(declare-datatypes () ((Value"
                + " (VByte (valueByte Int))"
                + " (VChar (valueChar Int))"
                + " (VShort (valueShort Int))"
                + " (VInt (valueInt Int))"
                + " (VLong (valueLong Int))"
                + " (VFloat (valueFloat (_ FloatingPoint 8 24)))"
                + " (VDouble (valueDouble (_ FloatingPoint 11 53)))"
                + " (VBool (valueBool Bool))"
                + " (VRef (valueRef Ref))"
                + " (VString (valueString String)))))";
    }

    public static String boxIntegral(String value, String javaType) {
        String constructor = integralValuePart(javaType, true);
        return constructor.isEmpty() ? "" : "(" + constructor + " "
                + value + ")";
    }

    public static String unboxIntegral(String value, String javaType) {
        String accessor = integralValuePart(javaType, false);
        return accessor.isEmpty() ? "" : "(" + accessor + " "
                + value + ")";
    }

    /**
     * The tag a boxed container cell of {@code javaType} may be unboxed by,
     * or {@code ""} when it must stay boxed.
     *
     * <p>A cell whose declared type names a primitive sort is an ordinary
     * Java value once unboxed, so arithmetic and ordering on it are exact.
     * Two cases deliberately answer {@code ""}: a type that names no sort at
     * all, and a reference cell.  {@code (VRef nullRef)} is also the value a
     * refused read leaves behind, so unboxing a reference cell would turn a
     * visible refusal into a formula built on a term that means nothing.</p>
     */
    public static String unboxableCellKind(String javaType) {
        String kind = valueKind(javaType);
        return "VRef".equals(kind) ? "" : kind;
    }

    public static String valueKind(String javaType) {
        String integral = integralValuePart(javaType, true);
        if (!integral.isEmpty()) return integral;
        String descriptor = JavaPrimitiveBoxing
                .primitiveDescriptor(javaType);
        if (descriptor.isEmpty()) {
            descriptor = JavaPrimitiveSmtSemantics
                    .javaTypeDescriptor(javaType);
        }
        if ("Z".equals(descriptor)) return "VBool";
        if ("F".equals(descriptor)) return "VFloat";
        if ("D".equals(descriptor)) return "VDouble";
        if ("Ljava/lang/String;".equals(descriptor)) return "VString";
        if ("L".equals(javaType) || descriptor.startsWith("L")
                || descriptor.startsWith("[")) {
            return "VRef";
        }
        return "";
    }

    private static String integralValuePart(
            String javaType, boolean constructor) {
        String descriptor = JavaPrimitiveBoxing
                .primitiveDescriptor(javaType);
        if (descriptor.isEmpty()) {
            descriptor = JavaPrimitiveSmtSemantics
                    .javaTypeDescriptor(javaType);
        }
        String name = "B".equals(descriptor) ? "Byte"
                : "C".equals(descriptor) ? "Char"
                : "S".equals(descriptor) ? "Short"
                : "I".equals(descriptor) ? "Int"
                : "J".equals(descriptor) ? "Long" : "";
        return name.isEmpty() ? ""
                : (constructor ? "V" : "value") + name;
    }

    public static List<String> preamble() {
        return Collections.unmodifiableList(Arrays.asList(
                "(declare-datatypes () ((IndexedState"
                        + " (mkIndexedState"
                        + " (indexed_size Int)"
                        + " (indexed_elements (Array Int Value))))))",
                "(declare-datatypes () ((AssocState"
                        + " (mkAssocState"
                        + " (assoc_size Int)"
                        + " (assoc_present (Array Value Bool))"
                        + " (assoc_values (Array Value Value))"
                        + " (assoc_order (Array Int Value))"
                        + " (assoc_position (Array Value Int))))))",
                "(declare-fun indexed_state_of (Ref) IndexedState)",
                "(declare-fun assoc_state_of (Ref) AssocState)",
                "(define-fun indexed_read ((s IndexedState) (i Int)) Value"
                        + " (select (indexed_elements s) i))",
                "(define-fun indexed_write ((s IndexedState) (i Int)"
                        + " (v Value)) IndexedState"
                        + " (mkIndexedState (indexed_size s)"
                        + " (store (indexed_elements s) i v)))",
                "(define-fun indexed_append ((s IndexedState) (v Value))"
                        + " IndexedState (mkIndexedState"
                        + " (+ (indexed_size s) 1)"
                        + " (store (indexed_elements s)"
                        + " (indexed_size s) v)))",
                "(define-fun assoc_has ((s AssocState) (k Value)) Bool"
                        + " (select (assoc_present s) k))",
                "(define-fun assoc_read ((s AssocState) (k Value)) Value"
                        + " (select (assoc_values s) k))",
                "(define-fun assoc_key_at ((s AssocState) (i Int)) Value"
                        + " (select (assoc_order s) i))",
                "(define-fun assoc_value_at ((s AssocState) (i Int)) Value"
                        + " (assoc_read s (assoc_key_at s i)))",
                "(define-fun assoc_put ((s AssocState) (k Value)"
                        + " (v Value)) AssocState"
                        + " (mkAssocState"
                        + " (ite (assoc_has s k) (assoc_size s)"
                        + " (+ (assoc_size s) 1))"
                        + " (store (assoc_present s) k true)"
                        + " (store (assoc_values s) k v)"
                        + " (ite (assoc_has s k) (assoc_order s)"
                        + " (store (assoc_order s) (assoc_size s) k))"
                        + " (ite (assoc_has s k) (assoc_position s)"
                        + " (store (assoc_position s) k"
                        + " (assoc_size s)))))"
                ,
                associativeRemoveDefinition()
        ));
    }

    private static String associativeRemoveDefinition() {
        return "(define-fun assoc_remove ((s AssocState) (k Value))"
                + " AssocState"
                + " (ite (assoc_has s k)"
                + " (let ((p (select (assoc_position s) k)))"
                + " (mkAssocState"
                + " (- (assoc_size s) 1)"
                + " (store (assoc_present s) k false)"
                + " (assoc_values s)"
                + " (lambda ((q Int))"
                + " (ite (and (<= p q)"
                + " (< q (- (assoc_size s) 1)))"
                + " (select (assoc_order s) (+ q 1))"
                + " (select (assoc_order s) q)))"
                + " (lambda ((q Value))"
                + " (ite (= q k) (- 1)"
                + " (ite (and (assoc_has s q)"
                + " (> (select (assoc_position s) q) p))"
                + " (- (select (assoc_position s) q) 1)"
                + " (select (assoc_position s) q))))))"
                + " s))";
    }

    public static Term unboxValue(Term value, String javaType, Sort cellSort,
                           Host host) {
        if (value == null || value.sort != Sort.VALUE) return value;
        String kind = valueKind(javaType);
        if (!kind.isEmpty()) {
            host.require("((_ is " + kind + ") " + value.text + ")");
        }
        String integralValue = unboxIntegral(value.text, javaType);
        if (!integralValue.isEmpty()) {
            return new Term(integralValue, Sort.INT,
                    JavaPrimitiveSmtSemantics.widthOfJavaType(javaType));
        }
        if (cellSort == Sort.BOOL) {
            return new Term("(valueBool " + value.text + ")", Sort.BOOL);
        }
        if (cellSort == Sort.REF) {
            return new Term("(valueRef " + value.text + ")", Sort.REF);
        }
        if (cellSort == Sort.FLOAT32) {
            return new Term("(valueFloat " + value.text + ")", Sort.FLOAT32);
        }
        if (cellSort == Sort.FLOAT64) {
            return new Term("(valueDouble " + value.text + ")",
                    Sort.FLOAT64);
        }
        if (cellSort == Sort.STRING) {
            return new Term("(valueString " + value.text + ")", Sort.STRING);
        }
        return value;
    }
}
