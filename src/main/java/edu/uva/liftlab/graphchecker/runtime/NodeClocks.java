package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Clock;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

final class NodeClocks {
    private static final class Jump {
        private final Clock clock;
        private final long place;
        private final long skew;

        private Jump(Clock clock, long place, long skew) {
            this.clock = clock;
            this.place = place;
            this.skew = skew;
        }
    }

    private static final Map<String, List<Jump>> JUMPS =
            new ConcurrentHashMap<String, List<Jump>>();

    private NodeClocks() {
    }

    static long skew(String node, Clock clock, long place) {
        List<Jump> jumps = JUMPS.get(node);
        if (jumps == null || place <= 0L) return 0L;
        synchronized (jumps) {
            Jump latest = null;
            for (Jump jump : jumps) {
                if (jump.place > place || !jump.clock.same(clock)) {
                    continue;
                }
                if (latest == null || jump.place >= latest.place) {
                    latest = jump;
                }
            }
            return latest == null ? 0L : latest.skew;
        }
    }

    static boolean jump(String node, Clock clock, long place, long skew) {
        if (place <= 0L || clock.source().isEmpty()) return false;
        List<Jump> jumps = JUMPS.computeIfAbsent(node,
                key -> new ArrayList<Jump>());
        synchronized (jumps) {
            jumps.add(new Jump(clock, place, skew));
        }
        return true;
    }
}
