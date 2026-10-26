package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.plan.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
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

final class PlantSites {
    static final class Call {
        final String siteId;
        final String callee;
        final String javaType;
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

        String key() {
            return siteId + "\n" + callee + "\n"
                    + (clock == null ? "" : clock.toString());
        }
    }

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
    private final Map<String, Integer> invocations =
            new LinkedHashMap<String, Integer>();
    private final Map<String, Map<String, Set<String>>> fields =
            new LinkedHashMap<String, Map<String, Set<String>>>();

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
            for (JsonElement element : array(task,
                    ConfiguredSourcePhaseContract.PLAN_FIELD)) {
                if (element.isJsonObject()) {
                    read.phase(element.getAsJsonObject());
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

    private void phase(JsonObject phase) {
        if (!ConfiguredSourcePhaseContract.CONFIG_PLAN_AUTHORITY.equals(
                optionalString(phase, "authority"))) {
            return;
        }
        fields.computeIfAbsent(optionalString(phase, "sourceId"),
                key -> new LinkedHashMap<String, Set<String>>())
                .computeIfAbsent(optionalString(phase, "fieldSignature"),
                        key -> new LinkedHashSet<String>())
                .add(optionalString(phase, "siteId"));
    }

    private void invocation(JsonObject action, String occurrence) {
        String port = optionalString(action, "portId");
        int planned = optionalInteger(action, "replayOccurrence", -1);
        if (port.isEmpty() || occurrence.isEmpty() || planned < 1) return;
        try {
            invocations.put(port + "|" + OccurrenceAddress.parse(occurrence)
                    .id(), planned);
        } catch (IllegalArgumentException notAnAddress) {
        }
    }

    int invocation(String port, OccurrenceAddress occurrence) {
        return invocations.getOrDefault(port + "|" + occurrence.id(), 1);
    }

    List<Call> calls(String port) {
        Map<String, Call> distinct = new LinkedHashMap<String, Call>();
        for (Call call : calls.getOrDefault(port,
                Collections.<Call>emptyList())) {
            distinct.putIfAbsent(call.key(), call);
        }
        return new ArrayList<Call>(distinct.values());
    }

    Set<String> locations(String port) {
        return locations.getOrDefault(port, Collections.<String>emptySet());
    }

    Set<String> sites(String port) {
        return sites.getOrDefault(port, Collections.<String>emptySet());
    }

    Map<String, Set<String>> fields(String rootId) {
        return fields.getOrDefault(rootId,
                Collections.<String, Set<String>>emptyMap());
    }

    Capture capture(String port) {
        return captures.get(port);
    }

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
