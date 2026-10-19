package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.explore.Corpus;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;

final class StaleRuns {
    private final Corpus corpus;
    private final StaticScopeMap scope;
    private final Map<List<Object>, String> reasons =
            new ConcurrentHashMap<List<Object>, String>();

    StaleRuns(Corpus corpus, StaticScopeMap scope) {
        this.corpus = corpus;
        this.scope = scope;
    }

    String reason(String sessionId, JsonObject read) {
        JsonObject location = read.has("location")
                && read.get("location").isJsonObject()
                ? read.getAsJsonObject("location") : new JsonObject();
        return reason(sessionId, Corpus.readSite(read),
                edu.uva.liftlab.graphchecker.smt.JsonFields.primitiveString(
                        read, "_java_type"),
                SmtLowering.kindOf(location));
    }

    String reason(String sessionId, String readSite, String javaType,
                  LocationKind kind) {
        Set<String> stale = corpus.staleRuns(sessionId);
        if (stale.isEmpty() || readSite.isEmpty()) return "";
        return reasons.computeIfAbsent(Arrays.<Object>asList(sessionId,
                readSite, javaType, kind), key -> {
            Set<String> writers = new TreeSet<String>();
            for (String carrier : scope.carriersAt(readSite, javaType,
                    kind)) {
                for (StaticScopeMap.Site site : scope.writersOf(carrier)) {
                    for (String occurrence : stale) {
                        if (scope.regionHolds(OccurrenceAddress.parse(
                                occurrence).regionId(), site)) {
                            writers.add(occurrence);
                        }
                    }
                }
            }
            return writers.isEmpty() ? "" : STALE + writers;
        });
    }

    static final String STALE = "a version no write row states, read where"
            + " an occurrence holding a write site of its carrier ran"
            + " unplanned or for its doors alone, which the exploration now"
            + " runs whole: the value may be its write, free, never held: ";
}
