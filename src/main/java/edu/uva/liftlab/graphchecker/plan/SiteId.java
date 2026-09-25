package edu.uva.liftlab.graphchecker.plan;

import edu.uva.liftlab.graphchecker.smt.JsonFields;

/** {@code <method>#u<unitIndex>}: the project-wide name of one bytecode site.
 *  {@link #of} refuses a blank method or negative unit; {@link #render} allows
 *  the {@code -1} "no unit of its own" sentinel for private keys and messages.
 */
public final class SiteId {
    private static final String UNIT_MARKER = "#u";
    /** The member every row publishes a site under (defined only here). */
    public static final String MEMBER = "siteId";

    private SiteId() {
    }

    /** The site id of one unit of one method. */
    public static String of(String method, int unitIndex) {
        if (unitIndex < 0) {
            throw new IllegalArgumentException(
                    "unitIndex must be non-negative");
        }
        return render(method, unitIndex);
    }

    /** {@link #of} tolerating the {@code -1} sentinel; never for a published
     *  site id. */
    public static String render(String method, int unitIndex) {
        return JsonFields.requireText(method, "method")
                + UNIT_MARKER + unitIndex;
    }

    /** The method one site id names, or "" when it names no unit. */
    public static String methodOf(String siteId) {
        int marker = siteId == null ? -1 : siteId.lastIndexOf(UNIT_MARKER);
        return marker < 0 || unitIndexOf(siteId) < 0 ? ""
                : siteId.substring(0, marker);
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
