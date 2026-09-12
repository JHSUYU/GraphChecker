package edu.uva.liftlab.graphchecker.concolic;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * The {@code --name value} command line every concolic entry point is
 * launched with.
 *
 * <p>Each entry point used to scan its own argv, and they disagreed about
 * what a malformed one is -- one refused a bare option, one refused only a
 * missing value, one said "--name value" and another said "--key value".
 * A campaign launches them all the same way, so they read a command line
 * the same way.</p>
 */
final class CliArgs {
    private CliArgs() {
    }

    /**
     * The pairs of one command line.  Every option carries a value, so an
     * argument that does not begin {@code --}, and an option at the end of
     * the line with nothing after it, are both refused by name.
     */
    static Map<String, String> pairs(String[] argv) {
        Map<String, String> values = new LinkedHashMap<>();
        for (int index = 0; argv != null && index < argv.length; index++) {
            String option = argv[index];
            if (option == null || !option.startsWith("--")
                    || index + 1 >= argv.length) {
                throw new IllegalArgumentException(
                        "Expected --name value, got " + option);
            }
            values.put(option.substring(2), argv[++index]);
        }
        return values;
    }
}
