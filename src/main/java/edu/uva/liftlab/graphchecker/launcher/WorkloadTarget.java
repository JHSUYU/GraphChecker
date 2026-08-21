package edu.uva.liftlab.graphchecker.launcher;

import edu.uva.liftlab.graphchecker.causynth.ExceptionTargetAnnotationScanner;
import edu.uva.liftlab.graphchecker.causynth.ExceptionTargetSite;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/**
 * The annotated target the workload is expected to reach.
 *
 * <p>Resolution goes through the analysis's own scanner, so the launcher and
 * the analysis agree on what {@code hdfs-11741} means by construction. An
 * unresolved id is a prerequisite failure, reported before the workload
 * starts: a run whose target is not even declared in the compiled source
 * cannot produce a target outcome, and finding that out after a multi-minute
 * interpreted workload wastes the run.</p>
 *
 * <p>The class also owns the trace predicates. A streamed trace row records
 * its method as a Soot signature, {@code <class: returnType name(args)>}, so
 * class and method name together identify the target method within a run;
 * overloads are not distinguished, which is enough for a reach question and
 * is reported as such rather than dressed up as branch-level evidence.</p>
 */
public final class WorkloadTarget {

    private final ExceptionTargetSite site;
    private final String classMarker;
    private final String methodMarker;
    private final String throwMarker;

    private WorkloadTarget(ExceptionTargetSite site) {
        this.site = site;
        this.classMarker = "\"<" + site.className() + ": ";
        this.methodMarker = " " + site.methodName() + "(";
        this.throwMarker = "\"runtimeType\":\"" + site.exceptionClass() + "\"";
    }

    /**
     * Finds the single {@code @CausynthExceptionTarget(id)} in the inputs.
     *
     * @param classInputs directories or jars of compiled application classes
     */
    public static WorkloadTarget resolve(String exceptionTargetId,
                                         List<Path> classInputs)
            throws LauncherException {
        String wanted = exceptionTargetId == null
                ? "" : exceptionTargetId.trim();
        if (wanted.isEmpty()) {
            throw new LauncherException(LauncherDiagnostic.USAGE,
                    "exception target id is blank");
        }
        List<String> inputs = new ArrayList<>();
        for (Path input : classInputs) {
            inputs.add(input.toString());
        }
        List<ExceptionTargetSite> scanned;
        try {
            scanned = ExceptionTargetAnnotationScanner.scan(inputs);
        } catch (IOException failure) {
            throw new LauncherException(
                    LauncherDiagnostic.TARGET_SITE_UNRESOLVED,
                    "cannot scan " + inputs + " for @CausynthExceptionTarget",
                    failure);
        }
        List<ExceptionTargetSite> matches = new ArrayList<>();
        for (ExceptionTargetSite candidate : scanned) {
            if (wanted.equals(candidate.id())) {
                matches.add(candidate);
            }
        }
        if (matches.size() != 1) {
            List<String> declared = new ArrayList<>();
            for (ExceptionTargetSite candidate : scanned) {
                declared.add((candidate.id().isEmpty()
                        ? "<unnamed>" : candidate.id())
                        + "=" + candidate.stableIdentity());
            }
            throw new LauncherException(
                    LauncherDiagnostic.TARGET_SITE_UNRESOLVED,
                    "expected exactly one @CausynthExceptionTarget(\"" + wanted
                            + "\") in " + inputs + ", found " + matches.size()
                            + "; declared targets: " + declared);
        }
        return new WorkloadTarget(matches.get(0));
    }

    public ExceptionTargetSite site() {
        return site;
    }

    /** Human-readable identity of the target method. */
    public String methodKey() {
        return site.className() + "#" + site.methodName()
                + site.methodDescriptor();
    }

    /** Whether one streamed trace row belongs to the target method. */
    public boolean mentionedBy(String traceLine) {
        return traceLine != null
                && traceLine.contains(classMarker)
                && traceLine.contains(methodMarker);
    }

    /**
     * Whether one streamed trace row is the target method exiting with the
     * annotated exception type.
     */
    public boolean thrownBy(String traceLine) {
        return mentionedBy(traceLine)
                && traceLine.contains("\"event\":\"METHOD_EXIT_THROW\"")
                && traceLine.contains(throwMarker);
    }
}
