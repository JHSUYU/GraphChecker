package edu.uva.liftlab.graphchecker.concolic;

/**
 * Converts the two method-location formats used by the Soot planner and the
 * concolic VM into a common, descriptor-independent identity.
 *
 * <p>Soot emits signatures such as
 * {@code <example.Handler: void handle(java.lang.Object)>}, while the VM
 * records locations such as
 * {@code virtual void example.Handler.handle(jobject):42}.  The VM erases
 * reference descriptors, so class plus method name is the strongest stable
 * identity available at import time.</p>
 */
public final class ConcolicCodePosition {
    private ConcolicCodePosition() {
    }

    /** Returns {@code class#method}, or an empty string for an unknown format. */
    public static String sootMethodKey(String signature) {
        if (signature == null) {
            return "";
        }
        String value = signature.trim();
        int classStart = value.startsWith("<") ? 1 : 0;
        int colon = value.indexOf(':', classStart);
        int arguments = value.indexOf('(', colon + 1);
        if (colon < 0 || arguments < 0) {
            return "";
        }
        int methodStart = value.lastIndexOf(' ', arguments);
        if (methodStart < colon) {
            return "";
        }
        String owner = value.substring(classStart, colon).trim()
                .replace('/', '.');
        String method = value.substring(methodStart + 1, arguments).trim();
        return owner.isEmpty() || method.isEmpty()
                ? "" : owner + "#" + method;
    }

    /** Returns {@code class#method}, or an empty string for an unknown format. */
    public static String vmMethodKey(String codePosition) {
        if (codePosition == null) {
            return "";
        }
        String value = codePosition.trim().replace('/', '.');
        int arguments = value.indexOf('(');
        if (arguments < 0) {
            return "";
        }
        int tokenStart = value.lastIndexOf(' ', arguments);
        String qualified = value.substring(tokenStart + 1, arguments).trim();
        int separator = qualified.lastIndexOf('.');
        if (separator <= 0 || separator + 1 >= qualified.length()) {
            return "";
        }
        return qualified.substring(0, separator) + "#"
                + qualified.substring(separator + 1);
    }

    public static boolean matches(String sootSignature, String codePosition) {
        String planned = sootMethodKey(sootSignature);
        return !planned.isEmpty() && planned.equals(vmMethodKey(codePosition));
    }
}
