package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * The case's {@code symbolic-inputs.jsonl}: the one authority on manual roots.
 *
 * <p>A declaration says where a symbol enters, not what the failure reads, so
 * it is not derived from the backward slice: a healthy run can take the arm
 * that writes nothing, which no walk over recorded flows reaches (hdfs-11741's
 * {@code removeExpiredKeys}).</p>
 *
 * <p>Rule: <b>a declared input's method is a region root by declaration</b>, in
 * the static slice, the skeleton weave, runtime selection and the plan closure,
 * whether or not the slice reaches it. A declared method the recording never
 * entered is refused by name (never an invented activation). Only reader of the
 * method column; others go through {@link #declaredMethod}.</p>
 */
public final class DeclaredSymbolicInputs {
    /** Root authority of a declared method nothing else roots; consulted last,
     *  since region ids are minted from the authority and must not be renamed.
     */
    public static final String AUTHORITY = "DECLARED_INPUT_ENTRY";

    /** Region-row member marking a declared root; later stages read this, not
     *  the case file. */
    public static final String ROOT_FIELD = "declaredInputRoot";

    /** {@code admissionBasis} of an occurrence planned only because its root is
     *  declared. */
    public static final String ADMISSION = "DECLARED_SYMBOLIC_INPUT_V1";

    private static final String PROPERTY = "causynth.symbolic.inputs";
    private static final String ENVIRONMENT = "CAUSYNTH_SYMBOLIC_INPUTS";

    private DeclaredSymbolicInputs() {
    }

    /** The Soot signature a row names: whole in {@code method}, or {@code
     *  class} plus the {@code returnType name(args)} half; "" when the row
     *  names a region. */
    public static String declaredMethod(JsonObject row) throws IOException {
        String method = firstNonBlank(optionalString(row, "method"));
        if (method.isEmpty()) return "";
        if (method.startsWith("<")) {
            if (!method.endsWith(">") || !method.contains(": ")) {
                throw new IOException("symbolic input selection method "
                        + "is not a signature: " + method);
            }
            return method;
        }
        String declaring = firstNonBlank(optionalString(row, "class"));
        if (declaring.isEmpty()) {
            throw new IOException("symbolic input selection names a "
                    + "method with no declaring class: " + method);
        }
        return "<" + declaring + ": " + method + ">";
    }

    /** The CALLEE a row names, or "": every read of its return, anywhere in
     *  scope, is a root -- the form a clock needs, since a clock read in an
     *  unlisted method would otherwise be a constant. The kind comes from the
     *  row, never from the callee name. */
    public static String declaredCallee(JsonObject row) throws IOException {
        String callee = firstNonBlank(optionalString(row, "callee"));
        if (callee.isEmpty()) return "";
        if (!callee.startsWith("<") || !callee.endsWith(">")
                || !callee.contains(": ")) {
            throw new IOException("symbolic input selection callee is not a "
                    + "signature: " + callee);
        }
        return callee;
    }

    /** The cell a callee declaration names: its return. */
    public static String returnCell(String callee) {
        return callee == null || callee.isEmpty() ? "" : callee + ".return";
    }

    /** Every declared callee with its kind, in file order; two kinds for one
     *  callee is refused. */
    public static Map<String, String> callees(Path path) throws IOException {
        Map<String, String> declared = new LinkedHashMap<>();
        if (path == null) return declared;
        for (JsonObject row : ArtifactIO.readJsonl(path)) {
            String callee = declaredCallee(row);
            if (callee.isEmpty()) continue;
            String kind = firstNonBlank(optionalString(row, "kind"));
            String held = declared.put(callee, kind);
            if (held != null && !held.equals(kind)) {
                throw new IOException("symbolic input selection declares "
                        + callee + " at two kinds: " + held + " and " + kind);
            }
        }
        return declared;
    }

    /** Declared callees of the configured case; same key and refusal as {@link
     *  #configured}. */
    public static Map<String, String> configuredCallees() {
        String configured = firstNonBlank(System.getProperty(PROPERTY),
                System.getenv(ENVIRONMENT), "");
        if (configured.isEmpty()) return Collections.emptyMap();
        Path path = Paths.get(configured);
        try {
            return callees(path);
        } catch (IOException | RuntimeException unreadable) {
            throw new IllegalStateException(
                    "DECLARED_INPUT_FILE_UNREADABLE: cannot read the case's "
                            + "symbolic input declarations from " + path,
                    unreadable);
        }
    }

    /** The kind a CLOCK declaration states. */
    public static final String CLOCK_KIND = "CLOCK";

    /** Every method signature the declaration file names, in file order. */
    public static Set<String> methods(Path path) throws IOException {
        Set<String> methods = new LinkedHashSet<>();
        if (path == null) return methods;
        for (JsonObject row : ArtifactIO.readJsonl(path)) {
            String method = declaredMethod(row);
            if (!method.isEmpty()) methods.add(method);
        }
        return methods;
    }

    /** Declared methods of the configured case. An unset key declares none
     *  (legal); an unreadable file is refused by name, never read as "none". */
    public static Set<String> configured() {
        String configured = firstNonBlank(System.getProperty(PROPERTY),
                System.getenv(ENVIRONMENT), "");
        if (configured.isEmpty()) return Collections.emptySet();
        Path path = Paths.get(configured);
        try {
            return methods(path);
        } catch (IOException | RuntimeException unreadable) {
            throw new IllegalStateException(
                    "DECLARED_INPUT_FILE_UNREADABLE: cannot read the case's "
                            + "symbolic input declarations from " + path,
                    unreadable);
        }
    }
}
