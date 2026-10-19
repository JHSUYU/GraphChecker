package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.RunSpellings;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

final class RunNames {
    private static volatile RunSpellings spellings = RunSpellings.NONE;

    private RunNames() {
    }

    private static final Set<String> UNSTATED = new HashSet<String>();

    static synchronized void spelled(String node, String spelling) {
        spellings = spellings.with(node, spelling);
    }

    static final class Keyed {
        final String location;
        final String unnamed;

        private Keyed(String location, String unnamed) {
            this.location = location;
            this.unnamed = unnamed;
        }
    }

    static Keyed key(String location) {
        String keyed = spellings.name(location == null ? "" : location);
        return new Keyed(keyed, RunSpellings.unnamed(keyed));
    }

    static String name(String text) {
        return spellings.name(text);
    }

    static Map<String, String> stated() {
        return spellings.asMap();
    }

    static synchronized boolean firstUnstated(String unnamed) {
        return UNSTATED.add(unnamed);
    }
}
