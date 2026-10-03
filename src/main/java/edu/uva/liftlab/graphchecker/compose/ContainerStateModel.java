package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.uva.liftlab.graphchecker.compose.ContainerSmtCodec.Host;
import edu.uva.liftlab.graphchecker.compose.ContainerSmtCodec.Sort;
import edu.uva.liftlab.graphchecker.compose.ContainerSmtCodec.Term;

/**
 * THE CONTAINER STATE MODEL: the {@code Value}, {@code IndexedState} and
 * {@code AssocState} datatypes and functions, and the one boxing between a
 * Java cell and a {@code Value}.  It reads no recorded expression; lowering
 * container operations is {@link ContainerSmtCodec}'s.
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
     * The cell that holds Java null: an absent element, a refused read's
     * residue, and a {@code null} leaf compared against cells.
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
     * The tag a boxed cell of {@code javaType} may be unboxed by, or
     * {@code ""} to stay boxed: unknown types and reference cells, since
     * {@code (VRef nullRef)} is also a refused read's residue.
     */
    public static String unboxableCellKind(String javaType) {
        String kind = valueKind(javaType);
        return "VRef".equals(kind) ? "" : kind;
    }

    /** The {@code Value} constructor a cell of this Java type is boxed by. */
    private static String valueKind(String javaType) {
        String integral = integralValuePart(javaType, true);
        if (!integral.isEmpty()) return integral;
        String descriptor = cellDescriptor(javaType);
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

    /** A wrapper as the primitive it boxes, anything else as itself. */
    private static String cellDescriptor(String javaType) {
        String descriptor = JavaPrimitiveBoxing
                .primitiveDescriptor(javaType);
        return descriptor.isEmpty()
                ? JavaPrimitiveSmtSemantics.javaTypeDescriptor(javaType)
                : descriptor;
    }

    private static String integralValuePart(
            String javaType, boolean constructor) {
        String descriptor = cellDescriptor(javaType);
        String name = "B".equals(descriptor) ? "Byte"
                : "C".equals(descriptor) ? "Char"
                : "S".equals(descriptor) ? "Short"
                : "I".equals(descriptor) ? "Int"
                : "J".equals(descriptor) ? "Long" : "";
        return name.isEmpty() ? ""
                : (constructor ? "V" : "value") + name;
    }

    public static List<String> preamble() {
        return ORDERED;
    }

    /**
     * What reads a map's iteration order.  A query that reaches none of
     * these never asks it, and no operation of its maps keeps the order
     * ({@link #unordered}).
     */
    public static final Set<String> ORDER_READERS =
            Collections.unmodifiableSet(new LinkedHashSet<String>(
                    Arrays.asList("assoc_key_at", "assoc_position_of",
                            "assoc_view_key", "assoc_view_position")));

    /**
     * One preamble line as a query that reads no map's order
     * ({@link #ORDER_READERS}) needs it: a put or a removal leaves the order
     * and the positions as they were.  Nothing reads them and no state is
     * compared or chosen whole ({@code ContainerSmtCodec#term}), so the
     * query is the same question; but a removal's renumbering is a lambda
     * over arrays, and z3 answers a query holding one "incomplete (theory
     * array)" or not at all (hdfs-11741 L1: valuation 0 undecided on two
     * fatal-observing paths, sat in seconds without it).
     */
    public static String unordered(String line) {
        String kept = UNORDERED.get(line);
        return kept == null ? line : kept;
    }

    private static final String KEPT_ORDER = "(assoc_order s)";
    private static final String KEPT_POSITION = "(assoc_position s)";

    private static List<String> preamble(boolean ordered) {
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
                // An append under a guard (a stream's filtered member), the
                // guard inside the store as assoc_put_if's: with g false
                // the state is s's.
                "(define-fun indexed_append_if ((s IndexedState) (v Value)"
                        + " (g Bool)) IndexedState"
                        + " (let ((n (indexed_size s)))"
                        + " (mkIndexedState (ite g (+ n 1) n)"
                        + " (store (indexed_elements s) n"
                        + " (ite g v (select (indexed_elements s) n))))))",
                "(define-fun assoc_has ((s AssocState) (k Value)) Bool"
                        + " (select (assoc_present s) k))",
                "(define-fun assoc_read ((s AssocState) (k Value)) Value"
                        + " (select (assoc_values s) k))",
                "(define-fun assoc_key_at ((s AssocState) (i Int)) Value"
                        + " (select (assoc_order s) i))",
                "(define-fun assoc_position_of ((s AssocState) (k Value))"
                        + " Int (select (assoc_position s) k))",
                // A view's positions where the chain's order is not the
                // one the map's class iterates in: whatever bijection with
                // its keys the view facts state, and no order
                // (ContainerSmtCodec.ViewOrder.FREE).
                "(declare-fun assoc_view_key (AssocState Int) Value)",
                "(declare-fun assoc_view_position (AssocState Value) Int)",
                // Every array-valued choice is pushed inside a store: an
                // array-valued ite with a symbolic condition and a lambda
                // branch is outside what z3 decides (hdfs-11741 v79).
                "(define-fun assoc_put ((s AssocState) (k Value)"
                        + " (v Value)) AssocState"
                        + " (let ((h (not (assoc_has s k)))"
                        + " (n (assoc_size s)))"
                        + " (mkAssocState"
                        + " (ite h (+ n 1) n)"
                        + " (store (assoc_present s) k true)"
                        + " (store (assoc_values s) k v)"
                        + (ordered ? " (store (assoc_order s) n"
                        + " (ite h k (select (assoc_order s) n)))"
                        + " (store (assoc_position s) k"
                        + " (ite h n (select (assoc_position s) k)))"
                        : " " + KEPT_ORDER + " " + KEPT_POSITION)
                        + ")))",
                // A removal under a guard: the guard is pushed INSIDE the
                // renumbering lambdas, and with h false every component is
                // s's own.
                "(define-fun assoc_remove_if ((s AssocState) (k Value)"
                        + " (g Bool)) AssocState"
                        + " (let ((h (and g (assoc_has s k)))"
                        + " (p (select (assoc_position s) k))"
                        + " (n (assoc_size s)))"
                        + " (mkAssocState"
                        + " (ite h (- n 1) n)"
                        + " (store (assoc_present s) k"
                        + " (and (not h) (assoc_has s k)))"
                        + " (assoc_values s)"
                        + (ordered ? " (lambda ((q Int))"
                        + " (ite (and h (<= p q) (< q (- n 1)))"
                        + " (select (assoc_order s) (+ q 1))"
                        + " (select (assoc_order s) q)))"
                        + " (lambda ((q Value))"
                        + " (ite (and h (= q k)) (- 1)"
                        + " (ite (and h (assoc_has s q)"
                        + " (> (select (assoc_position s) q) p))"
                        + " (- (select (assoc_position s) q) 1)"
                        + " (select (assoc_position s) q))))"
                        : " " + KEPT_ORDER + " " + KEPT_POSITION)
                        + ")))",
                "(define-fun assoc_remove ((s AssocState) (k Value))"
                        + " AssocState (assoc_remove_if s k true))",
                // A put under a guard, the guard inside each component as
                // assoc_remove_if's: with g false every component is s's.
                "(define-fun assoc_put_if ((s AssocState) (k Value)"
                        + " (v Value) (g Bool)) AssocState"
                        + " (let ((h (and g (not (assoc_has s k))))"
                        + " (n (assoc_size s)))"
                        + " (mkAssocState"
                        + " (ite h (+ n 1) n)"
                        + " (store (assoc_present s) k (or g (assoc_has s k)))"
                        + " (store (assoc_values s) k (ite g v (assoc_read s k)))"
                        + (ordered ? " (store (assoc_order s) n"
                        + " (ite h k (select (assoc_order s) n)))"
                        + " (store (assoc_position s) k"
                        + " (ite h n (select (assoc_position s) k)))"
                        : " " + KEPT_ORDER + " " + KEPT_POSITION)
                        + ")))"));
    }

    private static final List<String> ORDERED = preamble(true);

    /** Each line of {@link #ORDERED} that keeps the order, as it is kept
     *  by a query reading none. */
    private static final Map<String, String> UNORDERED = unorderedLines();

    private static Map<String, String> unorderedLines() {
        Map<String, String> lines = new LinkedHashMap<String, String>();
        List<String> kept = preamble(false);
        for (int at = 0; at < ORDERED.size(); at++) {
            if (!ORDERED.get(at).equals(kept.get(at))) {
                lines.put(ORDERED.get(at), kept.get(at));
            }
        }
        return Collections.unmodifiableMap(lines);
    }

    public static Term unboxValue(Term value, String javaType, Sort cellSort,
                           Host host) {
        if (value == null || value.sort != Sort.VALUE) return value;
        String kind = valueKind(javaType);
        if (cellSort == Sort.STRING) {
            // A String a container answers may be null (a value stored
            // null): the cell is a String or the null cell, and says which.
            String isNull = "(= " + value.text + " " + NULL_CELL + ")";
            host.require("(or ((_ is VString) " + value.text + ") " + isNull
                    + ")");
            return Term.string("(valueString " + value.text + ")", isNull);
        }
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
        return value;
    }
}
