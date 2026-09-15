package edu.uva.liftlab.graphchecker.runtime.d3;

/** The one string fact this package needs of its own. */
final class Text {
    private Text() {
    }

    static String safe(String value) {
        return value == null ? "" : value.trim();
    }

}
