package edu.uva.liftlab.graphchecker.causynth;

import java.nio.file.Path;

/** Resolved, immutable annotation-target context for one static run. */
final class CausynthTargetContext {
    final Path outputDir;
    final String seedException;
    final String exceptionTargetId;
    final ExceptionTargetSite exceptionTargetSite;
    final String analysisScope;

    CausynthTargetContext(Path outputDir,
                          String exceptionTargetId,
                          ExceptionTargetSite exceptionTargetSite,
                          String analysisScope) {
        this.outputDir = outputDir;
        this.exceptionTargetId = exceptionTargetId;
        this.exceptionTargetSite = exceptionTargetSite;
        this.seedException = exceptionTargetSite == null
                ? null : exceptionTargetSite.exceptionClass;
        this.analysisScope = analysisScope;
    }

    CausynthTargetContext withExceptionTarget(ExceptionTargetSite site) {
        return new CausynthTargetContext(outputDir,
                exceptionTargetId, site, analysisScope);
    }
}
