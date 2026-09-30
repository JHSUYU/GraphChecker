package edu.uva.liftlab.graphchecker.option;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * An engine main's {@code --name value} options ({@code --name=value} too; a
 * bare {@code --flag} is {@code "true"}).  Anything not starting with
 * {@code --} is skipped.  An option given more than once has every value in
 * {@link #all}, and its last one everywhere else.
 */
public final class LongOptions {
    private final Map<String, List<String>> values;

    private LongOptions(Map<String, List<String>> values) {
        this.values = values;
    }

    public static LongOptions parse(String[] argv) {
        Map<String, List<String>> values =
                new LinkedHashMap<String, List<String>>();
        for (int index = 0; index < argv.length; index++) {
            if (!argv[index].startsWith("--")) continue;
            String name = argv[index].substring(2);
            int equals = name.indexOf('=');
            String value;
            if (equals >= 0) {
                value = name.substring(equals + 1);
                name = name.substring(0, equals);
            } else if (index + 1 < argv.length
                    && !argv[index + 1].startsWith("--")) {
                value = argv[++index];
            } else {
                value = "true";
            }
            values.computeIfAbsent(name, ignored -> new ArrayList<String>())
                    .add(value);
        }
        return new LongOptions(values);
    }

    /** The option's value; {@code fallback} when absent or blank. */
    public String value(String name, String fallback) {
        List<String> given = values.get(name);
        String value = given == null ? null : given.get(given.size() - 1);
        return value == null || value.trim().isEmpty() ? fallback : value;
    }

    /** Every value the option was given, in order; none when absent. */
    public List<String> all(String name) {
        List<String> given = values.get(name);
        return given == null ? Collections.<String>emptyList()
                : Collections.unmodifiableList(given);
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
