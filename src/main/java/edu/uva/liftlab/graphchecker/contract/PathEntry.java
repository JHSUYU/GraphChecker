package edu.uva.liftlab.graphchecker.contract;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public final class PathEntry {
    private final String pathId;
    private final String sessionId;
    private final String selector;
    private final boolean fatalObserved;
    private final List<String> restsOn;
    private final long cutoff;

    private PathEntry(String pathId, String sessionId, String selector,
                      boolean fatalObserved, List<String> restsOn,
                      long cutoff) {
        this.pathId = pathId;
        this.sessionId = sessionId;
        this.selector = selector;
        this.fatalObserved = fatalObserved;
        this.restsOn = restsOn;
        this.cutoff = cutoff;
    }

    public static PathEntry of(String pathId, String sessionId, String selector,
                               boolean fatalObserved,
                               Collection<String> restsOn, long cutoff) {
        return new PathEntry(Fields.text(pathId, "pathId"),
                Fields.text(sessionId, "sessionId"),
                Fields.text(selector, "selector"), fatalObserved,
                new ArrayList<String>(restsOn), cutoff);
    }
}
