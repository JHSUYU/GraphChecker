package edu.uva.liftlab.graphchecker.contract;

/**
 * THE PORT ONE LEAF OF A STORE'S CONTENT CROSSES (SYMBOL-SCOPE §6.4): a
 * site, {@code <transport>#CONTENT:<location>#<pointer>}, the location as
 * the store's turn keys it and the leaf's JSON pointer (RFC 6901), each
 * {@code /} spelled {@code |} since a site spells no {@code /} or {@code @}
 * ({@link Frame}); {@code %}, {@code |} and {@code @} are escaped first.
 * Both the runtime that names an export or an attach by it and COMPOSE,
 * which reads the location back to name the view a leaf came through, use
 * this one spelling.
 */
public final class ContentPort {
    private static final String MARK = "#CONTENT:";

    /** One parsed port: its transport, location and pointer. */
    public static final class Parsed {
        public final String transport;
        public final String location;
        public final String pointer;

        private Parsed(String transport, String location, String pointer) {
            this.transport = transport;
            this.location = location;
            this.pointer = pointer;
        }
    }

    private ContentPort() {
    }

    /** The port of {@code pointer} in the document at {@code location}. */
    public static String of(String transport, String location,
                            String pointer) {
        return transport + MARK + site(location) + "#" + site(pointer);
    }

    /** The port a site spells, or null for no content port. */
    public static Parsed parse(String site) {
        if (!is(site)) return null;
        int mark = site.indexOf(MARK);
        String rest = site.substring(mark + MARK.length());
        int cut = rest.indexOf('#');
        return new Parsed(site.substring(0, mark),
                path(rest.substring(0, cut)), path(rest.substring(cut + 1)));
    }

    /** Whether a site spells a content port ({@link #parse} not null),
     *  without decoding it. */
    public static boolean is(String site) {
        int mark = site == null ? -1 : site.indexOf(MARK);
        return mark > 0 && site.indexOf('#', mark + MARK.length()) >= 0;
    }

    /** The half a view accessor's read stands at ({@link #viewed}). */
    private static final String VIEWED = "#VIEWED:";

    /**
     * The site one node's view accessor stands at when it hands out what
     * its decodes of {@code location} made (SYMBOL-SCOPE §6.4): {@code
     * <transport>#VIEWED:<location>}, spelled as {@link #of} spells it.
     */
    public static String viewed(String transport, String location) {
        return transport + VIEWED + site(location);
    }

    /** Whether {@code site} is a view accessor's ({@link #viewed}). */
    public static boolean viewed(String site) {
        return site != null && site.indexOf(VIEWED) > 0;
    }

    // Java 8's String.replace(CharSequence, CharSequence) compiles a
    // pattern per call: only where there is something to escape.
    private static String site(String path) {
        if (path.indexOf('%') < 0 && path.indexOf('|') < 0
                && path.indexOf('@') < 0) {
            return path.replace('/', '|');
        }
        return path.replace("%", "%25").replace("|", "%7C")
                .replace("@", "%40").replace('/', '|');
    }

    private static String path(String site) {
        if (site.indexOf('%') < 0) return site.replace('|', '/');
        return site.replace('|', '/').replace("%40", "@")
                .replace("%7C", "|").replace("%25", "%");
    }
}
