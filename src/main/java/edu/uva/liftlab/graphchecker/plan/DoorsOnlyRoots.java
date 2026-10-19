package edu.uva.liftlab.graphchecker.plan;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

public final class DoorsOnlyRoots {
    public static final String PROPERTY = "causynth.doors.only.roots";

    private final Set<String> methods;

    private DoorsOnlyRoots(Set<String> methods) {
        this.methods = methods;
    }

    public static DoorsOnlyRoots current() {
        return of(System.getProperty(PROPERTY, ""));
    }

    public static DoorsOnlyRoots of(String value) {
        Set<String> methods = new LinkedHashSet<String>();
        for (String method : value.split("\\|")) {
            if (!method.trim().isEmpty()) methods.add(method.trim());
        }
        return new DoorsOnlyRoots(Collections.unmodifiableSet(methods));
    }

    public boolean holds(String rootMethod) {
        return rootMethod != null && methods.contains(rootMethod);
    }
}
