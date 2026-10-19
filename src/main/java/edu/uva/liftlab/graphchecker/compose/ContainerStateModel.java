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

public final class ContainerStateModel {
    private ContainerStateModel() {
    }

    static boolean emptiesState(String operation) {
        return "CLEAR".equals(operation) || "SNAPSHOT_BASE".equals(operation);
    }

    public static final String NULL_CELL = "(VRef nullRef)";

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

    public static String stringRef(String string) {
        return "(string_ref " + string + ")";
    }

    public static String stringRefFacts(String string) {
        String ref = stringRef(string);
        return "(and (= (ref_string " + ref + ") " + string + ") (not (= "
                + ref + " nullRef)))";
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

    public static String unboxableCellKind(String javaType) {
        String kind = valueKind(javaType);
        return "VRef".equals(kind) ? "" : kind;
    }

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

    public static final Set<String> ORDER_READERS =
            Collections.unmodifiableSet(new LinkedHashSet<String>(
                    Arrays.asList("assoc_key_at", "assoc_position_of")));

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
                "(declare-fun string_ref (String) Ref)",
                "(declare-fun ref_string (Ref) String)",
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
                "(declare-fun assoc_view_key (Int Int Int) Value)",
                "(declare-fun assoc_view_position (Int Int Value) Int)",
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
        if (cellSort == Sort.REF) {
            String string = "(valueString " + value.text + ")";
            host.require("(or ((_ is VRef) " + value.text + ") ((_ is VString) "
                    + value.text + "))");
            host.require("(=> ((_ is VString) " + value.text + ") "
                    + stringRefFacts(string) + ")");
            return new Term("(ite ((_ is VRef) " + value.text + ") (valueRef "
                    + value.text + ") " + stringRef(string) + ")", Sort.REF);
        }
        if (cellSort == Sort.STRING) {
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
