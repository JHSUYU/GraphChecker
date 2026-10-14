package edu.uva.liftlab.graphchecker.contract;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A class name the JVM mints per run is not an identity: strips the counter
 * from reflection accessors ({@code GeneratedMethodAccessor23}) and lambda
 * proxies ({@code Foo$$Lambda$14/0x..}), whose numbers depend on unrelated
 * inflation and would make one site differ across recordings (spurious
 * {@link edu.uva.liftlab.graphchecker.explore.Corpus}{@code .affected}; a
 * Solr client's pooled send named a different anchor in each recording).
 * The classes a weave desugars a lambda into ({@code
 * Foo$lambda_execute_0__1734091262}) keep their number: every weave names
 * them by content (GraphChecker's {@code LambdaClassNames}), so a runtime
 * site spells its class as every run and the static artifacts do.
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
        if (!accessor && !lambda) return className;
        String stable = className;
        // "$1" is the group: the accessor's own name without its number.
        if (accessor) stable = ACCESSOR.matcher(stable).replaceAll("$1");
        // "$$Lambda" is LITERAL text, so it is quoted: unquoted, "$$" is a
        // group reference and the replacement throws.
        if (lambda) {
            stable = LAMBDA.matcher(stable).replaceAll(
                    Matcher.quoteReplacement("$$Lambda"));
        }
        return stable;
    }

    /**
     * Whether a method ({@code <a.B: R m(A)>}, a frame's or Soot's
     * signature) is a synthetic hop between the method that wrote a call and
     * the one it runs: javac's {@code access$NNN} or lambda body {@code
     * lambda$m$N}, or a method of Soot's desugared lambda class ({@code
     * X$lambda_m_N__k}, whose {@code call()} or {@code run()} forwards to
     * the lambda's body).  A helper such a hop calls is called from the
     * method that wrote the call: the one rule {@code runtime.Identity
     * #callerFrame} and a decider's {@code via} ({@code
     * causynth.BooleanReturns}) share.
     */
    public static boolean syntheticHop(String method) {
        if (method == null) return false;
        int colon = method.indexOf(':');
        int paren = method.indexOf('(', colon + 1);
        if (colon < 0 || paren < 0) return false;
        if (method.substring(0, colon).contains("$lambda_")) return true;
        String head = method.substring(colon + 1, paren).trim();
        String name = head.substring(head.lastIndexOf(' ') + 1);
        return name.startsWith("access$") || name.startsWith("lambda$");
    }
}
