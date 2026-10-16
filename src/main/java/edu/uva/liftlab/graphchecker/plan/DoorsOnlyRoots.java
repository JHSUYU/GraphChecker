package edu.uva.liftlab.graphchecker.plan;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * THE SYSTEM'S HEAVY REGION ROOTS: the region roots a system names whose
 * occurrences always run for their doors alone ({@value #PROPERTY}, its
 * {@code system.sh} {@code doors_only_roots}; a per-system declaration,
 * listed in STATUS).  Planned whole, such an occurrence's replay tracks
 * every write of everything it builds: SGF8-adhoc-14's seed planned seven
 * of Solr's {@code CoreContainer.create} whole for the {@code
 * inFlightCreations} set they add to and remove from, and their 109,222
 * writes -- 89 % of the session, 499 MB against 76 MB before -- held the
 * seed replay 36 min against 9.5.  Run for its doors, such an occurrence's
 * ZooKeeper and HTTP doors still stand (their faults among them), and a
 * value it writes is the recording's, named where a demand reaches it
 * ({@code causynth.RuntimeSelectedRegionFinalizer#stateDoorsOnly}, {@code
 * explore.ClosurePlanner}).
 */
public final class DoorsOnlyRoots {
    /** The system property naming them: methods ({@code <owner: ...>})
     *  separated by '|'. */
    public static final String PROPERTY = "causynth.doors.only.roots";

    private final Set<String> methods;

    private DoorsOnlyRoots(Set<String> methods) {
        this.methods = methods;
    }

    /** The roots {@value #PROPERTY} names; none where it is unset. */
    public static DoorsOnlyRoots current() {
        return of(System.getProperty(PROPERTY, ""));
    }

    /** The roots a {@value #PROPERTY} value names. */
    public static DoorsOnlyRoots of(String value) {
        Set<String> methods = new LinkedHashSet<String>();
        for (String method : value.split("\\|")) {
            if (!method.trim().isEmpty()) methods.add(method.trim());
        }
        return new DoorsOnlyRoots(Collections.unmodifiableSet(methods));
    }

    /** Whether a region rooted at {@code rootMethod} runs for its doors
     *  alone. */
    public boolean holds(String rootMethod) {
        return rootMethod != null && methods.contains(rootMethod);
    }
}
