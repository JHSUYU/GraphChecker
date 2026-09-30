package edu.uva.liftlab.graphchecker.causynth;

import java.nio.file.Path;

/** One static run's output directory and the exception target it slices. */
final class CausynthTargetContext {
    final Path outputDir;
    final String seedException;
    final ExceptionTargetSite exceptionTargetSite;

    CausynthTargetContext(Path outputDir,
                          ExceptionTargetSite exceptionTargetSite) {
        this.outputDir = outputDir;
        this.exceptionTargetSite = exceptionTargetSite;
        this.seedException = exceptionTargetSite.exceptionClass;
    }
}
