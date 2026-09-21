package edu.uva.liftlab.graphchecker.contract;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A class name the JVM mints PER RUN is not an identity.
 *
 * <p>Two kinds of class are named by the runtime rather than by the
 * program, and the name carries a counter that starts over in every JVM:
 * the reflection accessors {@code sun.reflect.GeneratedMethodAccessor23},
 * {@code GeneratedConstructorAccessor7} and
 * {@code GeneratedSerializationConstructorAccessor4}, minted when a
 * reflective call is inflated, and the lambda proxies
 * {@code com.example.Foo$$Lambda$14/1234567890}, minted at the first
 * execution of each {@code invokedynamic}.  How far the counter has got
 * depends on how many OTHER reflective calls or lambdas that JVM happened
 * to inflate first, which no flip and no workload decides.  Everything
 * else is left exactly as it was: this normalizes two spellings the VM
 * invented, and nothing about the program.</p>
 *
 * <p>Why it matters, measured.  An endpoint's site embeds the class name
 * of the method the event stood in, so a write inside an inflated
 * reflective call is a DIFFERENT site in every recording -- for no reason
 * the exploration can act on.  On the hdfs-11741 campaign #3 corpus that
 * defect reached the frontier through {@link
 * edu.uva.liftlab.graphchecker.explore.Corpus}{@code .affected}, which asks
 * whether a replay's world changed the structure of what a region
 * received: <b>75 of the 187 affected (task, session) pairs of wave 2, and
 * 8 of the 11 worlds the witness arm {@code dn1
 * removeExpiredKeys#u15#1 -> false} was owed in, came from nothing but
 * {@code GeneratedMethodAccessor23} against {@code
 * GeneratedMethodAccessor22} in one write site.</b>  With the number gone
 * the count falls to 112 and the arm is owed exactly where nn0's rotation
 * changed what the DataNode received.</p>
 *
 * <p>Applied AT THE MINT, in the runtime, never in {@link Endpoint} or
 * {@link Frame} parsing: a row already on disk keeps the spelling it was
 * written with, and the contract stays a plain codec that reads back what
 * some run wrote.</p>
 *
 * <p>It is text-level and idempotent, so it may be given a bare class name
 * or a whole site id that embeds one ({@code
 * sun.reflect.GeneratedMethodAccessor23#invoke()V#56:WRITE}); a name with
 * neither spelling in it is returned unchanged, and the common case costs
 * one {@code indexOf}.</p>
 */
public final class JvmNames {
    /** {@code sun.reflect.Generated*Accessor<NN>} -- the inflation counter. */
    private static final Pattern ACCESSOR = Pattern.compile(
            "(GeneratedSerializationConstructorAccessor"
                    + "|GeneratedConstructorAccessor"
                    + "|GeneratedMethodAccessor)[0-9]+");
    /**
     * {@code <Outer>$$Lambda$<NN>/<hash>} -- the proxy counter.
     *
     * <p>The separator before the hash is the VM's {@code /}, which is NOT
     * a package separator; a caller that has already put the name in source
     * form has a {@code .} there instead, so both are taken.  That is also
     * why this is applied BEFORE {@code '/'} is turned into {@code '.'}
     * wherever a converter has the choice.</p>
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
        // The common case is neither, and this runs once per recorded
        // event: two indexOf calls rather than two regex matchers.
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
}
