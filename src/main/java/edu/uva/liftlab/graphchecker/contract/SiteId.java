package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.concolic.JsonFields;

/**
 * {@code <method>#u<unitIndex>}: the project-wide name of one bytecode
 * site, shared by the static analysis, the instrumented recorder, the
 * concolic runtime and every artifact that keys on a site.
 *
 * <p>A site is a real unit of a real method, so a blank method or a
 * negative unit index is refused rather than rendered: {@code #u7} and
 * {@code m#u-1} are not sites, and a caller that cannot name one has to
 * say so itself -- the callers that may not have a unit index already test
 * for that before asking for a site id.  {@link #render} spells the same
 * form for the private keys and diagnostics that legitimately carry the
 * instrumentation's {@code -1} "no unit of its own" sentinel.</p>
 */
public final class SiteId {
    private static final String UNIT_MARKER = "#u";
    /**
     * The member every row publishes a site under.
     *
     * <p>Defined once, here, with the grammar it spells.  Two contracts held
     * their own {@code = "siteId"} constant, which is the drift this class
     * exists to prevent.</p>
     */
    public static final String MEMBER = "siteId";

    private SiteId() {
    }

    /** The site id of one unit of one method. */
    public static String of(String method, int unitIndex) {
        if (unitIndex < 0) {
            throw new IllegalArgumentException(
                    "unitIndex must be non-negative");
        }
        return JsonFields.requireText(method, "method")
                + UNIT_MARKER + unitIndex;
    }

    /**
     * The same spelling as {@link #of} for a <em>private</em> key or a
     * diagnostic message, tolerating the {@code -1} "this hook has no unit
     * of its own" sentinel the instrumentation passes for a materialization
     * whose accessor body lives outside the application classes.
     *
     * <p>Never use this for a site id an artifact publishes or another
     * stage keys on: those must name a real unit, and {@link #of} is the
     * rule that says so.  A blank method names nothing either way and is
     * refused here too.</p>
     */
    public static String render(String method, int unitIndex) {
        return JsonFields.requireText(method, "method")
                + UNIT_MARKER + unitIndex;
    }

    /** The unit index one site id names, or -1 when it names none. */
    public static int unitIndexOf(String siteId) {
        int marker = siteId == null ? -1 : siteId.lastIndexOf(UNIT_MARKER);
        int index = marker + UNIT_MARKER.length();
        if (marker < 0 || index >= siteId.length()) return -1;
        try {
            return Integer.parseInt(siteId.substring(index));
        } catch (NumberFormatException ignored) {
            return -1;
        }
    }
}
