package edu.uva.liftlab.graphchecker.causynth;

import java.nio.file.Path;

/** Resolved, immutable annotation-target context for one static run. */
final class CausynthTargetContext {
    final Path outputDir;
    final Path specPath;
    final String seedException;
    final String exceptionTargetId;
    final ExceptionTargetSite exceptionTargetSite;
    final String analysisScope;

    CausynthTargetContext(Path outputDir, Path specPath,
                          String exceptionTargetId,
                          ExceptionTargetSite exceptionTargetSite,
                          String analysisScope) {
        this.outputDir = outputDir;
        this.specPath = specPath;
        this.exceptionTargetId = exceptionTargetId;
        this.exceptionTargetSite = exceptionTargetSite;
        this.seedException = exceptionTargetSite == null
                ? null : exceptionTargetSite.exceptionClass;
        this.analysisScope = analysisScope;
    }

    CausynthTargetContext withExceptionTarget(ExceptionTargetSite site) {
        return new CausynthTargetContext(outputDir, specPath,
                exceptionTargetId, site, analysisScope);
    }
}
