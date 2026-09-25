package edu.uva.liftlab.graphchecker.option;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * An engine main's {@code --name value} options ({@code --name=value} too; a
 * bare {@code --flag} is {@code "true"}).  Anything not starting with
 * {@code --} is skipped.
 */
public final class LongOptions {
    private final Map<String, String> values;

    private LongOptions(Map<String, String> values) {
        this.values = values;
    }

    public static LongOptions parse(String[] argv) {
        Map<String, String> values = new LinkedHashMap<String, String>();
        for (int index = 0; index < argv.length; index++) {
            if (!argv[index].startsWith("--")) continue;
            String name = argv[index].substring(2);
            int equals = name.indexOf('=');
            if (equals >= 0) {
                values.put(name.substring(0, equals),
                        name.substring(equals + 1));
            } else if (index + 1 < argv.length
                    && !argv[index + 1].startsWith("--")) {
                values.put(name, argv[++index]);
            } else {
                values.put(name, "true");
            }
        }
        return new LongOptions(values);
    }

    /** The option's value; {@code fallback} when absent or blank. */
    public String value(String name, String fallback) {
        String value = values.get(name);
        return value == null || value.trim().isEmpty() ? fallback : value;
    }

    /** The option as a path; null when absent or blank. */
    public Path path(String name) {
        String value = value(name, null);
        return value == null ? null : Paths.get(value);
    }

    /** The option as a number; {@code fallback} when absent or blank. A passed
     *  value that is not a number is refused, never read as the default. */
    public long number(String name, long fallback) {
        String value = value(name, null);
        if (value == null) return fallback;
        try {
            return Long.parseLong(value.trim());
        } catch (NumberFormatException notANumber) {
            throw new IllegalArgumentException("--" + name + " was passed as"
                    + " \"" + value + "\", which is not a number: a"
                    + " mistyped bound is refused, never read as the default"
                    + " " + fallback, notANumber);
        }
    }
}
