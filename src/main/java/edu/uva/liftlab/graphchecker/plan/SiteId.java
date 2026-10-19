package edu.uva.liftlab.graphchecker.plan;

import edu.uva.liftlab.graphchecker.smt.JsonFields;

public final class SiteId {
    private static final String UNIT_MARKER = "#u";
    public static final String MEMBER = "siteId";

    private SiteId() {
    }

    public static String of(String method, int unitIndex) {
        if (unitIndex < 0) {
            throw new IllegalArgumentException(
                    "unitIndex must be non-negative");
        }
        return render(method, unitIndex);
    }

    public static String render(String method, int unitIndex) {
        return JsonFields.requireText(method, "method")
                + UNIT_MARKER + unitIndex;
    }

    public static String methodOf(String siteId) {
        int marker = siteId == null ? -1 : siteId.lastIndexOf(UNIT_MARKER);
        return marker < 0 || unitIndexOf(siteId) < 0 ? ""
                : siteId.substring(0, marker);
    }

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
