package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.plan.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * Where a native reproduction meets the values a replay mints, read off the
 * task plan (PIPELINE §10b): per input port, the call sites its value is the
 * return of -- an external call's ({@code CALL_RETURN}: a clock, a
 * configuration getter) or an unwoven accessor's -- each with its callee, its
 * JVM type, its declared clock and the region declaring it; per input port,
 * every location its actions name and every call site; per IN port, its
 * capture.  A site is the plan's own spelling, {@code <method>#u<unit>}
 * ({@link SiteId}), the one the recording weave states a call by.
 */
final class PlantSites {
    /** One call whose return is a port's value. */
    static final class Call {
        final String siteId;
        final String callee;
        final String javaType;
        /** A declared clock reading's clock (the replay mints it on its
         *  node's clock), else null. */
        final Clock clock;
        final String region;

        Call(String siteId, String callee, String javaType, Clock clock,
             String region) {
            this.siteId = siteId;
            this.callee = callee;
            this.javaType = javaType;
            this.clock = clock;
            this.region = region;
        }

        /** The call it is, whatever region declares it. */
        String key() {
            return siteId + "\n" + callee + "\n"
                    + (clock == null ? "" : clock.toString());
        }
    }

    /** One IN port's capture: where its value arrives. */
    static final class Capture {
        final String kind;
        final String siteId;
        final String callee;
        final String codecField;
        final Set<String> regions = new LinkedHashSet<String>();

        Capture(CommunicationHandoffSpec spec) {
            kind = spec.captureKind();
            siteId = spec.siteId();
            callee = spec.declaredCallee();
            codecField = spec.codecField();
        }
    }

    private final Map<String, List<Call>> calls =
            new LinkedHashMap<String, List<Call>>();
    private final Map<String, Set<String>> locations =
            new LinkedHashMap<String, Set<String>>();
    private final Map<String, Set<String>> sites =
            new LinkedHashMap<String, Set<String>>();
    private final Map<String, Capture> captures =
            new LinkedHashMap<String, Capture>();
    /** {@code <port>|<occurrence id>} -> the invocation its input action
     *  plans there ({@code replayOccurrence}). */
    private final Map<String, Integer> invocations =
            new LinkedHashMap<String, Integer>();

    private PlantSites() {
    }

    static PlantSites read(Path plan) throws IOException {
        PlantSites read = new PlantSites();
        for (JsonObject task : ArtifactIO.readJsonl(plan)) {
            String region = optionalString(task, "regionId");
            String occurrence = optionalString(task, "occurrenceId");
            for (JsonElement element : array(task,
                    InputActionCatalog.FIELD)) {
                if (element.isJsonObject()) {
                    read.action(element.getAsJsonObject(), region);
                    read.invocation(element.getAsJsonObject(), occurrence);
                }
            }
            for (CommunicationHandoffSpec spec
                    : CommunicationHandoffSpec.decode(task)) {
                if (spec.outgoing()) continue;
                read.captures.computeIfAbsent(spec.portId(),
                        port -> new Capture(spec)).regions.add(region);
            }
        }
        return read;
    }

    private void action(JsonObject action, String region) {
        String port = optionalString(action, "portId");
        if (port.isEmpty()) return;
        String site = optionalString(action, "siteId");
        if (!site.isEmpty()) {
            sites.computeIfAbsent(port, key -> new LinkedHashSet<String>())
                    .add(site);
        }
        String location = optionalString(action, "location");
        locations.computeIfAbsent(port, key -> new LinkedHashSet<String>())
                .add(location.isEmpty() ? "?" : location);
        String javaType = optionalString(action, "javaType");
        String accessor = optionalString(action, "accessorCallerMethod");
        int accessorUnit = optionalInteger(action, "accessorCallUnitIndex",
                -1);
        String accessorCallee = optionalString(action,
                "accessorDeclaredCallee");
        Call call = null;
        if ("CALL_RETURN".equals(location) && !site.isEmpty()
                && !optionalString(action, "declaredCallee").isEmpty()) {
            // A clock is a declared reading only where the recording read it
            // (SymbolizeAction#declaresWallClockRead).
            long nanos = optionalLongInteger(action,
                    InputActionCatalog.DECLARED_WALL_CLOCK, 0L);
            Clock clock = nanos > 0L && optionalBool(action, "observed", false)
                    ? Clock.of(nanos, optionalString(action,
                    InputActionCatalog.DECLARED_CLOCK_SOURCE)) : null;
            call = new Call(site, optionalString(action, "declaredCallee"),
                    javaType, clock, region);
        } else if (!accessor.isEmpty() && accessorUnit >= 0
                && !accessorCallee.isEmpty()) {
            call = new Call(SiteId.of(accessor, accessorUnit),
                    accessorCallee, javaType, null, region);
        }
        if (call != null) {
            calls.computeIfAbsent(port, key -> new ArrayList<Call>())
                    .add(call);
        }
    }

    private void invocation(JsonObject action, String occurrence) {
        String port = optionalString(action, "portId");
        int planned = optionalInteger(action, "replayOccurrence", -1);
        if (port.isEmpty() || occurrence.isEmpty() || planned < 1) return;
        try {
            invocations.put(port + "|" + OccurrenceAddress.parse(occurrence)
                    .id(), planned);
        } catch (IllegalArgumentException notAnAddress) {
            // A task of no occurrence address plans no invocation of one.
        }
    }

    /** The invocation a port's input action plans in an occurrence: its
     *  {@code replayOccurrence} there, else the first. */
    int invocation(String port, OccurrenceAddress occurrence) {
        return invocations.getOrDefault(port + "|" + occurrence.id(), 1);
    }

    /** The calls a port's value is the return of, one per call. */
    List<Call> calls(String port) {
        Map<String, Call> distinct = new LinkedHashMap<String, Call>();
        for (Call call : calls.getOrDefault(port,
                Collections.<Call>emptyList())) {
            distinct.putIfAbsent(call.key(), call);
        }
        return new ArrayList<Call>(distinct.values());
    }

    /** Every location a port's input actions name. */
    Set<String> locations(String port) {
        return locations.getOrDefault(port, Collections.<String>emptySet());
    }

    /** Every call site a port's input actions name. */
    Set<String> sites(String port) {
        return sites.getOrDefault(port, Collections.<String>emptySet());
    }

    Capture capture(String port) {
        return captures.get(port);
    }

    /**
     * Every declared clock reading of the plan, by call, with the regions
     * declaring it: a native run's clock readings that run on their node's
     * clock (the replay mints each).
     */
    Map<Call, Set<String>> clockReadings() {
        Map<String, Call> byKey = new LinkedHashMap<String, Call>();
        Map<String, Set<String>> regions =
                new LinkedHashMap<String, Set<String>>();
        for (List<Call> declared : calls.values()) {
            for (Call call : declared) {
                if (call.clock == null) continue;
                byKey.putIfAbsent(call.key(), call);
                regions.computeIfAbsent(call.key(),
                        key -> new LinkedHashSet<String>()).add(call.region);
            }
        }
        Map<Call, Set<String>> readings = new LinkedHashMap<Call, Set<String>>();
        for (Map.Entry<String, Call> entry : byKey.entrySet()) {
            readings.put(entry.getValue(), regions.get(entry.getKey()));
        }
        return readings;
    }
}
