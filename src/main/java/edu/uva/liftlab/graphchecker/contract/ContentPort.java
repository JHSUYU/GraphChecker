package edu.uva.liftlab.graphchecker.contract;

public final class ContentPort {
    private static final String MARK = "#CONTENT:";

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

    public static String of(String transport, String location,
                            String pointer) {
        return transport + MARK + site(location) + "#" + site(pointer);
    }

    public static Parsed parse(String site) {
        if (!is(site)) return null;
        int mark = site.indexOf(MARK);
        String rest = site.substring(mark + MARK.length());
        int cut = rest.indexOf('#');
        while (cut + 1 < rest.length() && rest.charAt(cut + 1) != '|') {
            int next = rest.indexOf('#', cut + 1);
            if (next < 0) break;
            cut = next;
        }
        return new Parsed(site.substring(0, mark),
                path(rest.substring(0, cut)), path(rest.substring(cut + 1)));
    }

    public static boolean is(String site) {
        int mark = site == null ? -1 : site.indexOf(MARK);
        return mark > 0 && site.indexOf('#', mark + MARK.length()) >= 0;
    }

    private static final String VIEWED = "#VIEWED:";

    public static String viewed(String transport, String location) {
        return transport + VIEWED + site(location);
    }

    public static boolean viewed(String site) {
        return site != null && site.indexOf(VIEWED) > 0;
    }

    public static String pointer(String pointer) {
        return site(pointer);
    }

    public static boolean covers(Iterable<String> prefixes, String spelled) {
        for (String prefix : prefixes) {
            if (prefix.isEmpty() || spelled.equals(prefix)
                    || spelled.startsWith(prefix + "|")) {
                return true;
            }
        }
        return false;
    }

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
