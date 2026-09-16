package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * The case's {@code symbolic-inputs.jsonl}: the one authority on which
 * methods hold a manual root.
 *
 * <p>Roots are manual.  The file says which sites of the workload the case
 * declares symbolic, and that declaration is a statement about the program,
 * not a consequence of the backward slice from the annotated target: the
 * slice answers "what does the failure read", while the declaration answers
 * "where does a symbol enter at all".  The two differ exactly where the
 * healthy recording took the arm the case is about -- hdfs-11741's {@code
 * removeExpiredKeys} reads the clock, decides an expiry, and removes nothing
 * in a healthy run, so it writes no field, exports no value, and no
 * demand-directed walk over recorded flows can ever reach it.</p>
 *
 * <p>Hence the rule this class exists to state: <b>a declared symbolic
 * input's method is a region root by declaration</b>.  PLAN's job of
 * deciding which regions are instrumented therefore includes every method a
 * row of this file names -- in the static slice ({@code
 * SeedBackwardStaticAnalyzer}), in the skeleton weave ({@code
 * SymbolicRegionPlanner}), in the runtime selection ({@code
 * CausynthTraceRecorder}) and in the plan's own closure ({@code
 * RuntimeSelectedRegionFinalizer}) -- independent of whether the backward
 * slice reaches it.  The one thing the engine will not do for a declaration
 * is invent an activation: a declared method the recording never entered is
 * refused by name, because that is the workload's fault and not the
 * engine's.</p>
 *
 * <p>This is the only reader of the file's method column.  {@code
 * ConcolicScheduler} resolves the same spelling through {@link
 * #declaredMethod} so PLAN and the static passes cannot disagree about what
 * a row names.</p>
 */
public final class DeclaredSymbolicInputs {
    /**
     * Region root authority of a declared method nothing else roots.  It is
     * deliberately the last authority consulted: a declared method that is
     * already a failure target, task, fault or state-writer entry keeps that
     * authority, because the region id is minted from it and a declaration
     * must not rename a region the rest of the pipeline already addresses.
     */
    public static final String AUTHORITY = "DECLARED_INPUT_ENTRY";

    /**
     * Region-row member: this region's root method is named by a row of the
     * case's {@code symbolic-inputs.jsonl}.  It is the published form of the
     * declaration -- every stage after the static pass reads it off the
     * region skeleton rather than re-reading the case file, so there is one
     * decision and one artifact that carries it.
     */
    public static final String ROOT_FIELD = "declaredInputRoot";

    /**
     * {@code admissionBasis} of an activation the plan carries because its
     * root method is declared symbolic.  Nothing demands its outputs -- that
     * is the point -- so the basis is what tells a reader of the frozen plan
     * why the occurrence is there.
     */
    public static final String ADMISSION = "DECLARED_SYMBOLIC_INPUT_V1";

    /** Property/environment key naming the case's declaration file. */
    private static final String PROPERTY = "causynth.symbolic.inputs";
    private static final String ENVIRONMENT = "CAUSYNTH_SYMBOLIC_INPUTS";

    private DeclaredSymbolicInputs() {
    }

    /**
     * The canonical signature one declaration row names.
     *
     * <p>Either spelling is read: the whole Soot signature in {@code
     * method}, or {@code class} plus the method's own {@code returnType
     * name(argumentTypes)} half.  A row that names no method at all returns
     * {@code ""} -- it declared a region id instead, which is still read.</p>
     */
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

    /**
     * The declared methods of the configured case, for the static passes.
     *
     * <p>An unset key is a case that declares no symbolic input, which is a
     * legal case and the same condition {@code run_engine.sh} uses to decide
     * whether to pass the file on at all.  A key that names a file the pass
     * cannot read is refused by name rather than read back as "none": a
     * declaration that silently failed to arrive would plan regions the case
     * never asked for and drop the ones it did.</p>
     */
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
