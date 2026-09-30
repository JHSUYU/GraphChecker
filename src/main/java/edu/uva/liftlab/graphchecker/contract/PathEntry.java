package edu.uva.liftlab.graphchecker.contract;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * CONTRACT-SPEC §4: one composed consumer path and its selector,
 * {@code selector_p => pi_p and phi_fatal and reads_p}; per-session facts go
 * inside the implication, never global, and the tracked locations its fatal
 * predicate rests on ({@code restsOn}: what a confirming run is held to).
 * Written by Gson as part of {@link CompositionManifest}.
 */
public final class PathEntry {
    private final String pathId;
    private final String sessionId;
    private final String selector;
    private final boolean fatalObserved;
    private final List<String> restsOn;

    private PathEntry(String pathId, String sessionId, String selector,
                      boolean fatalObserved, List<String> restsOn) {
        this.pathId = pathId;
        this.sessionId = sessionId;
        this.selector = selector;
        this.fatalObserved = fatalObserved;
        this.restsOn = restsOn;
    }

    public static PathEntry of(String pathId, String sessionId, String selector,
                               boolean fatalObserved,
                               Collection<String> restsOn) {
        return new PathEntry(Fields.text(pathId, "pathId"),
                Fields.text(sessionId, "sessionId"),
                Fields.text(selector, "selector"), fatalObserved,
                new ArrayList<String>(restsOn));
    }
}
