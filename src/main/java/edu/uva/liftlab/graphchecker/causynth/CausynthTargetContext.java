package edu.uva.liftlab.graphchecker.causynth;

import java.nio.file.Path;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/** Resolved, immutable filesystem and seed context for one static run. */
final class CausynthTargetContext {
    final Path repoRoot;
    final Path moduleDir;
    final Path outputDir;
    final Path specPath;
    final List<String> seedVariables;
    final String seedFunction;
    final String seedException;
    final String exceptionTargetId;
    final ExceptionTargetSite exceptionTargetSite;
    final String analysisScope;
    final Path rpcMappingFile;

    CausynthTargetContext(Path repoRoot, Path moduleDir, Path outputDir,
                          Path specPath, List<String> seedVariables,
                          String seedFunction, String exceptionTargetId,
                          ExceptionTargetSite exceptionTargetSite,
                          String analysisScope, Path rpcMappingFile) {
        this.repoRoot = repoRoot;
        this.moduleDir = moduleDir;
        this.outputDir = outputDir;
        this.specPath = specPath;
        this.seedVariables = seedVariables;
        this.seedFunction = seedFunction;
        this.exceptionTargetId = exceptionTargetId;
        this.exceptionTargetSite = exceptionTargetSite;
        this.seedException = exceptionTargetSite == null
                ? null : exceptionTargetSite.exceptionClass;
        this.analysisScope = analysisScope;
        this.rpcMappingFile = rpcMappingFile;
    }

    CausynthTargetContext withExceptionTarget(ExceptionTargetSite site) {
        return new CausynthTargetContext(repoRoot, moduleDir, outputDir,
                specPath, seedVariables, seedFunction, exceptionTargetId,
                site, analysisScope, rpcMappingFile);
    }

    boolean hasSeed() {
        return seedException != null && !seedException.trim().isEmpty()
                || !seedVariables.isEmpty();
    }

    boolean exceptionSeeded() {
        return exceptionTargetSite != null;
    }

    String seedMode() {
        return exceptionSeeded()
                ? "EXCEPTION_ANNOTATION" : "VARIABLE";
    }

    String seedDescription() {
        return exceptionSeeded()
                ? seedException : String.valueOf(seedVariables);
    }

    String seedPredicate() {
        if (exceptionSeeded()) {
            return "throws " + seedException;
        }
        if (seedVariables.size() >= 2) {
            return seedVariables.get(0) + ".get("
                    + seedVariables.get(1) + ") == null";
        }
        return seedVariables.isEmpty() ? "" : seedVariables.get(0);
    }

    String seedMapName() {
        return seedVariables.isEmpty() ? "" : seedVariables.get(0);
    }

    String seedKeyExpression() {
        return seedVariables.size() < 2 ? "" : seedVariables.get(1);
    }

    String seedKeyMethodName() {
        Matcher dottedCall = Pattern.compile(
                "\\.\\s*([A-Za-z_][A-Za-z0-9_]*)\\s*\\(")
                .matcher(seedKeyExpression());
        if (dottedCall.find()) {
            return dottedCall.group(1);
        }
        Matcher bareCall = Pattern.compile(
                "^\\s*([A-Za-z_][A-Za-z0-9_]*)\\s*\\(")
                .matcher(seedKeyExpression());
        if (bareCall.find()) {
            return bareCall.group(1);
        }
        return "";
    }
}
