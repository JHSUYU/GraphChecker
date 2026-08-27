package edu.uva.liftlab.graphchecker.launcher;

import edu.uva.liftlab.graphchecker.causynth.ExceptionTargetAnnotationScanner;
import edu.uva.liftlab.graphchecker.causynth.ExceptionTargetSite;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/**
 * The annotated target the workload is expected to reach, and the trace
 * predicates that recognise it.  Resolution goes through the analysis's own
 * scanner, so the launcher and the analysis agree on what {@code hdfs-11741}
 * means by construction, and an unresolved id fails before the workload
 * starts.  A streamed row records its method as a Soot signature, so class and
 * method name together identify the target within a run; overloads are not
 * distinguished, which is enough for a reach question.
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
     * Finds the single {@code @CausynthExceptionTarget(wanted)} in the inputs.
     *
     * @param classInputs directories or jars of compiled application classes
     */
    public static WorkloadTarget resolve(String wanted,
                                         List<Path> classInputs)
            throws LauncherException {
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

    public ExceptionTargetSite site() { return site; }

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

    /** Whether one streamed row is the target method exiting with the
     *  annotated exception type. */
    public boolean thrownBy(String traceLine) {
        return mentionedBy(traceLine)
                && traceLine.contains("\"event\":\"METHOD_EXIT_THROW\"")
                && traceLine.contains(throwMarker);
    }
}
