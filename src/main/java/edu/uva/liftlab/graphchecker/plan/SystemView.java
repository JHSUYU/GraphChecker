package edu.uva.liftlab.graphchecker.plan;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * THE SYSTEM'S VIEW CLASSES: the classes a node builds its view of a shared
 * store with (a system's {@code system_scope}: Solr's ZkStateReader,
 * ClusterState, DocCollection, ...), named to SEED by {@value #PROPERTY}.
 * They are woven in every case for the store's decodes; the store's values
 * reach a target only as the ZooKeeper causal chain's leaves (owner
 * 2026-10-15: a finite set of fields, by the causal trace), so a reference
 * field only they write -- which decoded state the view holds -- is no
 * tracked cell ({@code causynth.RootDemand}, {@link StaticScopeMap}).
 */
public final class SystemView {
    /** The system property naming them, comma-separated class names. */
    public static final String PROPERTY = "causynth.system.view";

    private final Set<String> classes;

    private SystemView(Set<String> classes) {
        this.classes = classes;
    }

    /** The view {@value #PROPERTY} names; none where it is unset. */
    public static SystemView current() {
        return of(System.getProperty(PROPERTY, ""));
    }

    /** The view a {@value #PROPERTY} value names: comma-separated class
     *  names (EXPLORE's {@code --system-view}). */
    public static SystemView of(String names) {
        Set<String> classes = new LinkedHashSet<String>();
        for (String name : names.split(",")) {
            if (!name.trim().isEmpty()) classes.add(name.trim());
        }
        return new SystemView(Collections.unmodifiableSet(classes));
    }

    /** Whether a method ({@code <owner: ...>}) is a view class's, or a
     *  nested class's of one. */
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
