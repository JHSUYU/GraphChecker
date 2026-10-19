package edu.uva.liftlab.graphchecker.contract;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public final class JvmNames {
    private static final Pattern ACCESSOR = Pattern.compile(
            "(GeneratedSerializationConstructorAccessor"
                    + "|GeneratedConstructorAccessor"
                    + "|GeneratedMethodAccessor)[0-9]+");
    private static final Pattern LAMBDA = Pattern.compile(
            "\\$\\$Lambda\\$[0-9]+(?:[/.][0-9a-fA-Fx]+)?");

    private JvmNames() {
    }

    public static String stable(String className) {
        if (className == null || className.isEmpty()) return "";
        boolean accessor = className.indexOf("Accessor") >= 0;
        boolean lambda = className.indexOf("$$Lambda$") >= 0;
        if (!accessor && !lambda) return className;
        String stable = className;
        if (accessor) stable = ACCESSOR.matcher(stable).replaceAll("$1");
        if (lambda) {
            stable = LAMBDA.matcher(stable).replaceAll(
                    Matcher.quoteReplacement("$$Lambda"));
        }
        return stable;
    }

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
