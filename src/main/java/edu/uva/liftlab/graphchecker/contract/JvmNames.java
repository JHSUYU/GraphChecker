package edu.uva.liftlab.graphchecker.contract;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A class name the JVM or a weave mints per run is not an identity: strips
 * the counter from reflection accessors ({@code GeneratedMethodAccessor23}),
 * lambda proxies ({@code Foo$$Lambda$14/0x..}) and the classes a weave
 * desugars a lambda into ({@code Foo$lambda_execute_0__259}), whose numbers
 * depend on unrelated inflation or weave order and would make one site differ
 * across recordings (spurious
 * {@link edu.uva.liftlab.graphchecker.explore.Corpus}{@code .affected}; a
 * Solr client's pooled send named a different anchor in each recording).
 *
 * <p>Applied at the mint in the runtime, never when parsing
 * {@link Endpoint} or {@link Frame}.  Text-level and idempotent: takes a
 * class name or a whole site id.</p>
 */
public final class JvmNames {
    /** {@code sun.reflect.Generated*Accessor<NN>} -- the inflation counter. */
    private static final Pattern ACCESSOR = Pattern.compile(
            "(GeneratedSerializationConstructorAccessor"
                    + "|GeneratedConstructorAccessor"
                    + "|GeneratedMethodAccessor)[0-9]+");
    /**
     * {@code <Outer>$$Lambda$<NN>/<hash>}; the {@code /} is not a package
     * separator, so source-form {@code .} is accepted too.  Apply before
     * converting {@code '/'} to {@code '.'}.
     */
    private static final Pattern LAMBDA = Pattern.compile(
            "\\$\\$Lambda\\$[0-9]+(?:[/.][0-9a-fA-Fx]+)?");

    /**
     * {@code <Outer>$lambda_<method>_<n>__<counter>}: the weave's class for
     * the n-th lambda of a method, numbered by a counter over the whole weave.
     * The n tells two lambdas of one method apart and stays.
     */
    private static final Pattern DESUGARED = Pattern.compile(
            "(\\$lambda_[A-Za-z0-9_$]+?_[0-9]+)__[0-9]+");

    private JvmNames() {
    }

    /**
     * The same name with every per-run number taken out of it.
     *
     * @param className a VM/JVM class name, or a site id that embeds one
     * @return the stable spelling; the argument itself when it holds no
     *         run-minted name, and {@code ""} for null
     */
    public static String stable(String className) {
        if (className == null || className.isEmpty()) return "";
        // Runs per recorded event: cheap indexOf before any regex.
        boolean accessor = className.indexOf("Accessor") >= 0;
        boolean lambda = className.indexOf("$$Lambda$") >= 0;
        boolean desugared = className.indexOf("$lambda_") >= 0;
        if (!accessor && !lambda && !desugared) return className;
        String stable = className;
        // "$1" is the group: the accessor's own name without its number.
        if (accessor) stable = ACCESSOR.matcher(stable).replaceAll("$1");
        // "$$Lambda" is LITERAL text, so it is quoted: unquoted, "$$" is a
        // group reference and the replacement throws.
        if (lambda) {
            stable = LAMBDA.matcher(stable).replaceAll(
                    Matcher.quoteReplacement("$$Lambda"));
        }
        if (desugared) stable = DESUGARED.matcher(stable).replaceAll("$1");
        return stable;
    }
}
