package edu.uva.liftlab.graphchecker.causynth;


import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

/** Resolves workflow properties and target YAML into a target context. */
final class CausynthTargetResolver {
    private CausynthTargetResolver() {
    }

    /**
     * The target spec and the output directory the campaign declared.
     *
     * <p>Both arrive as system properties, which {@code run_engine.sh} sets
     * unconditionally from the one workflow config.  There used to be a
     * second config-file parser here, reached through
     * {@code firstNonBlank(property, config.get(key), literal)}: the property
     * always won, so neither the config branch nor its two literal defaults
     * ("target.yaml", "causynth-output/seed-backward") was reachable.  A
     * property the campaign does not set is refused by name instead.</p>
     */
    static CausynthTargetContext resolve() throws IOException {
        Path specPath = declaredPath("causynth.target.spec");
        return new CausynthTargetContext(declaredPath("causynth.output.dir"),
                exceptionTargetId(specPath), null);
    }

    private static Path declaredPath(String property) throws IOException {
        String declared = System.getProperty(property);
        if (declared == null || declared.trim().isEmpty()) {
            throw new IOException("the campaign declared no -D" + property);
        }
        return Paths.get(declared.trim()).toAbsolutePath().normalize();
    }

    /** The single {@code exception_target_id} of a target specification, or
     *  null when the file is absent. */
    private static String exceptionTargetId(Path path) throws IOException {
        if (!Files.isRegularFile(path)) {
            return null;
        }
        String exceptionTargetId = null;
        for (String line : Files.readAllLines(path,
                StandardCharsets.UTF_8)) {
            String trimmed = line.trim();
            if (trimmed.isEmpty() || trimmed.startsWith("#")) {
                continue;
            }
            int separator = trimmed.indexOf(':');
            if (line.startsWith(" ") || separator <= 0
                    || trimmed.endsWith(":")) {
                throw new IOException("Unsupported target specification "
                        + "entry: " + trimmed);
            }
            if (!"exception_target_id".equals(
                    trimmed.substring(0, separator).trim())
                    || exceptionTargetId != null) {
                throw new IOException("Target specification accepts only "
                        + "one exception_target_id");
            }
            exceptionTargetId = trimmed.substring(separator + 1).trim();
            if ((exceptionTargetId.startsWith("\"")
                    && exceptionTargetId.endsWith("\""))
                    || (exceptionTargetId.startsWith("'")
                    && exceptionTargetId.endsWith("'"))) {
                exceptionTargetId = exceptionTargetId.substring(1,
                        exceptionTargetId.length() - 1);
            }
        }
        return exceptionTargetId;
    }
}
