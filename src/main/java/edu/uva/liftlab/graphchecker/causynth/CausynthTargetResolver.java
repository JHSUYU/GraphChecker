package edu.uva.liftlab.graphchecker.causynth;


import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

/** Resolves the workflow properties and the target spec into a context. */
final class CausynthTargetResolver {
    private CausynthTargetResolver() {
    }

    /**
     * The output dir and the spec's one exception target, found in the
     * analysis inputs, as the system properties {@code run_engine.sh} always
     * sets; an unset one is refused by name.
     */
    static CausynthTargetContext resolve(List<String> inputs)
            throws IOException {
        Path spec = declaredPath("causynth.target.spec");
        List<ExceptionTargetLineResolver.TargetLine> targets =
                targetLines(spec);
        if (targets.size() != 1) {
            throw new IOException((targets.isEmpty()
                    ? "TARGET_SPEC_EMPTY" : "MULTI_TARGET_UNSUPPORTED")
                    + ": a static run slices from one exception_target; "
                    + spec + " declares " + targets.size());
        }
        return new CausynthTargetContext(declaredPath("causynth.output.dir"),
                ExceptionTargetLineResolver.resolve(inputs, targets.get(0)));
    }

    private static Path declaredPath(String property) throws IOException {
        String declared = System.getProperty(property);
        if (declared == null || declared.trim().isEmpty()) {
            throw new IOException("the campaign declared no -D" + property);
        }
        return Paths.get(declared.trim()).toAbsolutePath().normalize();
    }

    /**
     * The spec's {@code exception_target:} lines, in order.  Blank lines and
     * {@code #} comments are skipped; any other entry is refused.
     */
    static List<ExceptionTargetLineResolver.TargetLine> targetLines(Path spec)
            throws IOException {
        if (!Files.isRegularFile(spec)) {
            throw new IOException("the target spec does not exist: " + spec);
        }
        List<ExceptionTargetLineResolver.TargetLine> targets =
                new ArrayList<>();
        for (String line : Files.readAllLines(spec, StandardCharsets.UTF_8)) {
            String trimmed = line.trim();
            if (trimmed.isEmpty() || trimmed.startsWith("#")) {
                continue;
            }
            int separator = trimmed.indexOf(':');
            if (separator <= 0 || !"exception_target".equals(
                    trimmed.substring(0, separator).trim())) {
                throw new IOException("Unsupported target specification "
                        + "entry: " + trimmed + "; a target is "
                        + "exception_target: <name> <binary class name> "
                        + "<source line> [<thrown type>]");
            }
            targets.add(ExceptionTargetLineResolver.TargetLine.parse(
                    trimmed.substring(separator + 1)));
        }
        return targets;
    }
}
