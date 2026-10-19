package edu.uva.liftlab.graphchecker.plan;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

public final class SystemView {
    public static final String PROPERTY = "causynth.system.view";

    private final Set<String> classes;

    private SystemView(Set<String> classes) {
        this.classes = classes;
    }

    public static SystemView current() {
        return of(System.getProperty(PROPERTY, ""));
    }

    public static SystemView of(String names) {
        Set<String> classes = new LinkedHashSet<String>();
        for (String name : names.split(",")) {
            if (!name.trim().isEmpty()) classes.add(name.trim());
        }
        return new SystemView(Collections.unmodifiableSet(classes));
    }

    public boolean holds(String method) {
        if (method == null || !method.startsWith("<")) return false;
        int colon = method.indexOf(':');
        if (colon < 0) return false;
        String owner = method.substring(1, colon);
        int nested = owner.indexOf('$');
        return classes.contains(owner) || nested > 0
                && classes.contains(owner.substring(0, nested));
    }
}
