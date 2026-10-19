package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.annotation.Debug;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.plan.SystemView;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.smt.JavaContainerTypes;
import soot.SootMethod;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.strings;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.text;

final class RootDemand {
    static final String FILE = "root_demand.jsonl";
    static final int DISTANCE = 16;
    static final int WIDTH = 12;

    enum Kind {
        CLOCK, FAULT, CONFIG_CALL, CONFIG_FIELD, READ, TRACK, TRACK_IDENTITY,
        TRACK_CONTAINER, PROVENANCE, PRE_WINDOW, WIRE, IO, SCOPE, LIBRARY,
        CUT
    }

    static final String WIDTH_CUT = "WIDTH";
    static final String DISTANCE_CUT = "DISTANCE";
    static final String NO_SOURCE_CUT = "NO_SOURCE";
    static final String NO_DOOR_CUT = "NO_DOOR";
    static final String NO_REGION_CUT = "NO_REGION";
    static final String VALUE = "VALUE";
    static final String ESCAPE = "ESCAPE";
    static final String HANDLER = "HANDLER";

    interface Faults {
        Candidate valued(String siteId, String callee);

        List<Candidate> latent(Map<String, Integer> demanded,
                               Map<String, Integer> stores,
                               Set<String> path);

        String site(DemandedDoors.Site door);
    }

    static final class Candidate {
        final String siteId;
        final String callee;
        final String caller;
        final int ordinal;
        final int distance;
        final String reach;
        final boolean frontier;
        final List<String> via;
        final boolean placeable;

        Candidate(String siteId, String callee, String caller, int ordinal,
                  int distance, String reach, boolean frontier,
                  List<String> via, boolean placeable) {
            this.siteId = siteId;
            this.callee = callee;
            this.caller = caller;
            this.ordinal = ordinal;
            this.distance = distance;
            this.reach = reach;
            this.frontier = frontier;
            this.via = via;
            this.placeable = placeable;
        }

        Candidate at(int distance, String reach) {
            return new Candidate(siteId, callee, caller, ordinal, distance,
                    reach, frontier, via, placeable);
        }

        DemandedDoors.Site door() {
            return new DemandedDoors.Site(caller, callee, ordinal, distance,
                    reach, via);
        }
    }

    static final class Boundary {
        final Kind kind;
        final String cell;
        final String siteId;
        final String edgeKind;
        final int distance;
        boolean chosen;
        String cut = "";
        final String measured;

        private Boundary(Kind kind, String cell, String siteId,
                         String edgeKind, int distance) {
            this(kind, cell, siteId, edgeKind, distance, PATH);
        }

        private Boundary(Kind kind, String cell, String siteId,
                         String edgeKind, int distance, String measured) {
            this.kind = kind;
            this.cell = cell;
            this.siteId = siteId;
            this.edgeKind = edgeKind;
            this.distance = distance;
            this.measured = measured;
        }
    }

    static final String PATH = "PATH";
    static final String WRITERS = "WRITERS";
    private static final Set<Kind> TRACKED = java.util.EnumSet.of(Kind.TRACK,
            Kind.TRACK_IDENTITY, Kind.TRACK_CONTAINER, Kind.READ);

    private static final Set<String> RECEIVERS = new LinkedHashSet<>(
            Arrays.asList("accessor_receiver", "method_receiver",
                    "constructor_receiver", "dispatch_receiver",
                    "dispatch_caller_receiver"));
    private static final Set<String> OPERANDS = new LinkedHashSet<>(
            Arrays.asList("accessor_field_return", "local_def_use",
                    "container_receiver", "container_argument",
                    "library_receiver"));
    private static final Set<Kind> STORED = java.util.EnumSet.of(Kind.TRACK,
            Kind.TRACK_IDENTITY, Kind.TRACK_CONTAINER, Kind.READ);
    private static final Set<String> WRITES = new LinkedHashSet<>(
            Arrays.asList("field_write", "field_mutation",
                    "container_mutation_argument",
                    "container_call_mutation_effect",
                    "container_array_store_value", "container_publication"));
    private static final Pattern RETURN = Pattern.compile("^(<.+>)\\.return$");
    private static final Pattern FIELD = Pattern.compile(
            "^<([^:]+): (\\S+) ([^\\s(>]+)>$");
    private static final Pattern FORMAL = Pattern.compile(
            "^(<.+>)\\.param\\d+:.+$");
    private static final Pattern VALUE_LIKE = Pattern.compile(
            "^java\\.lang\\.(Boolean|Byte|Character|Short|Integer|Long"
                    + "|Float|Double|Number|String|CharSequence"
                    + "|StringBuilder|StringBuffer|Enum)$");
    private static final Pattern IO = Pattern.compile(
            "^(java|javax|sun|jdk)\\.\\S*(InputStream|Reader|File|Files"
                    + "|Channel|Socket|URLConnection)$");
    private static final String ATOMIC = "java.util.concurrent.atomic.";

    private final List<Boundary> boundaries;
    private final Set<String> configSources;
    private final List<DemandedDoors.Site> doors;
    private final Map<String, Integer> ioFrontier;

    private RootDemand(List<Boundary> boundaries, Set<String> configSources,
                       List<DemandedDoors.Site> doors,
                       Map<String, Integer> ioFrontier) {
        this.boundaries = Collections.unmodifiableList(boundaries);
        this.configSources = Collections.unmodifiableSet(configSources);
        this.doors = Collections.unmodifiableList(doors);
        this.ioFrontier = Collections.unmodifiableMap(ioFrontier);
    }

    static RootDemand of(List<Map<String, Object>> edges,
                         List<Map<String, Object>> regions,
                         Map<String, Clock> clocks, ConfigRoots config,
                         Set<String> pathSites,
                         Function<String, SharedFieldFlow.TrackedKind>
                                 trackedKind,
                         Predicate<String> constructionOnly,
                         Predicate<String> systemClass, Faults faults,
                         List<DemandedDoors.Site> woven) {
        Map<String, List<Map<String, Object>>> into = new HashMap<>();
        Set<String> carried = new LinkedHashSet<>();
        Set<String> starts = new LinkedHashSet<>();
        Set<String> path = new LinkedHashSet<>(pathSites);
        for (Map<String, Object> edge : edges) {
            into.computeIfAbsent(text(edge.get("toCell")),
                    ignored -> new ArrayList<>()).add(edge);
            if (OPERANDS.contains(text(edge.get("kind")))) {
                carried.add(text(edge.get("invoke")));
                carried.add(text(edge.get("accessorImplementationMethod")));
            }
            String kind = text(edge.get("kind"));
            if (("exception_guard".equals(kind)
                    || "guard_dependency".equals(kind))
                    && pathSites.contains(text(edge.get("siteId")))) {
                starts.add(text(edge.get("fromCell")));
            }
            if ("exception_throw".equals(text(edge.get("kind")))) {
                path.add(text(edge.get("siteId")));
            }
        }
        Set<String> regionMethods = new LinkedHashSet<>();
        Set<String> roots = new LinkedHashSet<>();
        for (Map<String, Object> region : regions) {
            regionMethods.addAll(strings(region.get("methods")));
            roots.add(text(region.get("rootMethod")));
        }
        Classifier classes = new Classifier(into, carried, regionMethods,
                roots, clocks, config, trackedKind, constructionOnly,
                systemClass);
        Map<String, Integer> demanded = new HashMap<>();
        List<Boundary> found = walk(into, starts, classes, demanded);
        choose(found);
        Set<String> chosenKeys = configuration(found, cone(into, starts),
                cone(into, writerGuards(found, into)), config, edges);
        List<DemandedDoors.Site> doors = new ArrayList<>(woven);
        Map<String, Integer> ioFrontier = doors(found, into, demanded, path,
                faults, doors);
        found.sort(Comparator.comparingInt((Boundary b) -> b.distance)
                .thenComparing(b -> b.kind.name())
                .thenComparing(b -> b.cell).thenComparing(b -> b.siteId)
                .thenComparing(b -> b.measured));
        return new RootDemand(found, chosenKeys, doors, ioFrontier);
    }

    private static Map<String, Integer> doors(
            List<Boundary> found, Map<String, List<Map<String, Object>>> into,
            Map<String, Integer> demanded, Set<String> path, Faults faults,
            List<DemandedDoors.Site> doors) {
        Map<Candidate, Boundary> candidates = new LinkedHashMap<>();
        for (Boundary boundary : found) {
            if (boundary.kind != Kind.IO) continue;
            Matcher returned = RETURN.matcher(boundary.cell);
            Candidate valued = returned.matches()
                    ? faults.valued(boundary.siteId, returned.group(1))
                    : null;
            if (valued == null) {
                boundary.cut = NO_DOOR_CUT;
            } else {
                candidates.put(valued.at(boundary.distance, VALUE),
                        boundary);
            }
        }
        Map<String, Integer> stores = new HashMap<>();
        for (Boundary boundary : found) {
            if (!boundary.chosen || !STORED.contains(boundary.kind)
                    || !FIELD.matcher(boundary.cell).matches()) {
                continue;
            }
            for (Map<String, Object> write : into.getOrDefault(boundary.cell,
                    Collections.<Map<String, Object>>emptyList())) {
                if (WRITES.contains(text(write.get("kind")))) {
                    stores.merge(text(write.get("siteId")),
                            boundary.distance, Math::min);
                }
            }
        }
        List<Boundary> latent = new ArrayList<>();
        for (Candidate candidate : faults.latent(demanded, stores, path)) {
            Boundary boundary = new Boundary(Kind.IO, candidate.callee
                    + FaultPropagation.THROWS, candidate.siteId,
                    candidate.frontier ? "fault_frontier"
                            : ESCAPE.equals(candidate.reach) ? "fault_escape"
                            : "fault_handler", candidate.distance);
            candidates.put(candidate, boundary);
            latent.add(boundary);
        }
        found.addAll(latent);
        Set<String> chosen = new LinkedHashSet<>();
        for (DemandedDoors.Site door : doors) {
            chosen.add(door.key());
            found.add(woven(door, faults.site(door)));
        }
        List<Candidate> ordered = new ArrayList<>(candidates.keySet());
        ordered.sort(Comparator.comparingInt((Candidate c) -> c.distance)
                .thenComparing(c -> c.siteId).thenComparing(c -> c.callee));
        Map<String, Integer> frontier = new LinkedHashMap<>();
        for (Candidate candidate : ordered) {
            Boundary boundary = candidates.get(candidate);
            String key = candidate.frontier ? candidate.callee
                    : candidate.door().key();
            boolean near = candidate.distance <= DISTANCE;
            if (candidate.frontier) {
                if (near && (frontier.containsKey(key)
                        || frontier.size() < WIDTH)) {
                    frontier.putIfAbsent(key, candidate.distance);
                }
                boundary.chosen = frontier.containsKey(key);
            } else {
                if (near && candidate.placeable && !chosen.contains(key)
                        && chosen.size() < WIDTH) {
                    chosen.add(key);
                    doors.add(candidate.door());
                }
                boundary.chosen = chosen.contains(key);
            }
            boundary.cut = boundary.chosen ? "" : !near ? DISTANCE_CUT
                    : candidate.placeable ? WIDTH_CUT : NO_REGION_CUT;
        }
        return frontier;
    }

    private static Boundary woven(DemandedDoors.Site door, String siteId) {
        Boundary boundary = new Boundary(Kind.IO, door.callee
                + FaultPropagation.THROWS, siteId, "door", door.distance);
        boundary.chosen = true;
        return boundary;
    }

    List<Boundary> boundaries() {
        return boundaries;
    }

    List<DemandedDoors.Site> doors() {
        return doors;
    }

    Set<String> configSources() {
        return configSources;
    }

    List<JsonObject> rows() {
        List<JsonObject> rows = new ArrayList<>();
        for (Boundary boundary : boundaries) {
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", 1);
            row.addProperty("kind", "ROOT_DEMAND_BOUNDARY");
            row.addProperty("class", boundary.kind.name());
            row.addProperty("distance", boundary.distance);
            row.addProperty("cell", boundary.cell);
            row.addProperty("siteId", boundary.siteId);
            row.addProperty("edgeKind", boundary.edgeKind);
            row.addProperty("chosen", boundary.chosen);
            row.addProperty("cut", boundary.cut);
            row.addProperty("measured", boundary.measured);
            rows.add(row);
        }
        return rows;
    }

    StaticScopeMap.Demand marks() {
        Map<String, Boundary> nearest = new LinkedHashMap<>();
        for (Boundary boundary : boundaries) {
            if (boundary.kind == Kind.CUT) continue;
            nearest.putIfAbsent(boundary.siteId + "\n" + boundary.cell,
                    boundary);
        }
        return (siteId, cell) -> {
            Boundary boundary = nearest.get(siteId + "\n" + cell);
            return boundary == null ? null : new StaticScopeMap.Demanded(
                    boundary.kind.name(), boundary.distance,
                    boundary.chosen);
        };
    }

    Map<String, StaticScopeMap.Demanded> frontier() {
        Map<String, StaticScopeMap.Demanded> frontier = new LinkedHashMap<>();
        for (Boundary boundary : boundaries) {
            if (!boundary.chosen) continue;
            Matcher returned = RETURN.matcher(boundary.cell);
            Matcher formal = FORMAL.matcher(boundary.cell);
            String signature = boundary.kind == Kind.PRE_WINDOW
                    || boundary.kind == Kind.PROVENANCE ? boundary.cell
                    : boundary.kind != Kind.SCOPE ? null
                    : returned.matches() ? returned.group(1)
                    : formal.matches() ? formal.group(1) : null;
            if (signature != null) {
                frontier.putIfAbsent(signature, new StaticScopeMap.Demanded(
                        boundary.kind.name(), boundary.distance, true));
            }
        }
        for (Map.Entry<String, Integer> io : ioFrontier.entrySet()) {
            frontier.putIfAbsent(io.getKey(), new StaticScopeMap.Demanded(
                    Kind.IO.name(), io.getValue(), true));
        }
        return frontier;
    }

    private static List<Boundary> walk(
            Map<String, List<Map<String, Object>>> into, Set<String> starts,
            Classifier classes, Map<String, Integer> demanded) {
        Map<String, Integer> distance = new HashMap<>();
        Map<String, Boundary> found = new LinkedHashMap<>();
        Deque<String> queue = new ArrayDeque<>();
        Set<String> copied = new HashSet<>();
        for (String start : starts) {
            distance.put(start, 0);
            queue.add(start);
        }
        while (!queue.isEmpty()) {
            String cell = queue.removeFirst();
            int next = distance.get(cell) + 1;
            boolean beyond = copied.contains(cell);
            for (Map<String, Object> edge : into.getOrDefault(cell,
                    Collections.<Map<String, Object>>emptyList())) {
                if (!classes.follows(edge)) continue;
                if (next > DISTANCE) {
                    found.putIfAbsent(Kind.CUT + "\n" + cell, new Boundary(
                            Kind.CUT, cell, "", "", DISTANCE));
                    break;
                }
                String from = text(edge.get("fromCell"));
                String site = text(edge.get("siteId"));
                if (!site.isEmpty()) demanded.merge(site, next, Math::min);
                Kind kind = classes.of(from, edge);
                boolean holds = beyond && kind == Kind.TRACK_CONTAINER
                        && !RETURN.matcher(from).matches();
                if (holds) kind = Kind.PROVENANCE;
                if (kind != null) {
                    String siteId = text(edge.get("siteId"));
                    found.putIfAbsent(kind + "\n" + from + "\n" + siteId,
                            new Boundary(kind, from, siteId,
                                    text(edge.get("kind")), next));
                    if (kind != Kind.PROVENANCE || holds) continue;
                }
                if (distance.putIfAbsent(from, next) == null) {
                    queue.addLast(from);
                    if (beyond || kind == Kind.PROVENANCE) copied.add(from);
                }
            }
        }
        return new ArrayList<>(found.values());
    }

    private static Map<String, Integer> cone(
            Map<String, List<Map<String, Object>>> into, Set<String> starts) {
        Map<String, Integer> at = new LinkedHashMap<>();
        for (String start : starts) at.put(start, 0);
        return cone(into, at);
    }

    private static Map<String, Integer> cone(
            Map<String, List<Map<String, Object>>> into,
            Map<String, Integer> starts) {
        Map<String, Integer> distance = new HashMap<>(starts);
        Deque<String> queue = new ArrayDeque<>(starts.keySet());
        while (!queue.isEmpty()) {
            String cell = queue.removeFirst();
            for (Map<String, Object> edge : into.getOrDefault(cell,
                    Collections.<Map<String, Object>>emptyList())) {
                String from = text(edge.get("fromCell"));
                if (distance.putIfAbsent(from, distance.get(cell) + 1)
                        == null) {
                    queue.addLast(from);
                }
            }
        }
        return distance;
    }

    private static Map<String, Integer> writerGuards(List<Boundary> found,
            Map<String, List<Map<String, Object>>> into) {
        Map<String, Integer> guards = new LinkedHashMap<>();
        for (Boundary boundary : found) {
            if (!boundary.chosen || !TRACKED.contains(boundary.kind)) {
                continue;
            }
            for (Map<String, Object> edge : into.getOrDefault(boundary.cell,
                    Collections.<Map<String, Object>>emptyList())) {
                if ("guard_dependency".equals(text(edge.get("kind")))) {
                    guards.putIfAbsent(text(edge.get("fromCell")), 1);
                }
            }
        }
        return guards;
    }

    private static Set<String> configuration(
            List<Boundary> found, Map<String, Integer> path,
            Map<String, Integer> writers, ConfigRoots config,
            List<Map<String, Object>> edges) {
        Map<String, String> keys = new HashMap<>();
        Map<String, Boundary> onPath = sources(path, PATH, config, edges,
                keys);
        Map<String, Boundary> atWriters = sources(writers, WRITERS, config,
                edges, keys);
        Set<String> chosen = nearest(onPath, keys,
                Collections.<String>emptySet());
        chosen.addAll(nearest(atWriters, keys, chosen));
        found.removeIf(boundary -> (boundary.kind == Kind.CONFIG_FIELD
                || boundary.kind == Kind.CONFIG_CALL)
                && (keys.containsKey(boundary.cell)
                || keys.containsKey(boundary.siteId)));
        for (Boundary boundary : found) {
            if (boundary.kind == Kind.CONFIG_FIELD
                    || boundary.kind == Kind.CONFIG_CALL) {
                boundary.cut = NO_SOURCE_CUT;
            }
        }
        for (Map<String, Boundary> measured : Arrays.asList(onPath,
                atWriters)) {
            Map<String, Integer> keyDistance = keyDistances(measured, keys);
            for (Map.Entry<String, Boundary> source : measured.entrySet()) {
                Boundary boundary = source.getValue();
                String key = keys.get(source.getKey());
                boundary.chosen = chosen.contains(key);
                boundary.cut = boundary.chosen ? ""
                        : keyDistance.get(key) > DISTANCE ? DISTANCE_CUT
                        : WIDTH_CUT;
                found.add(boundary);
            }
        }
        return chosen;
    }

    private static Map<String, Boundary> sources(
            Map<String, Integer> cone, String measured, ConfigRoots config,
            List<Map<String, Object>> edges, Map<String, String> keys) {
        Map<String, Boundary> sources = new LinkedHashMap<>();
        for (Map.Entry<String, ConfigRoots.Source> field
                : config.fields().entrySet()) {
            Integer at = cone.get(field.getKey());
            if (at == null) continue;
            sources.put(field.getKey(), new Boundary(Kind.CONFIG_FIELD,
                    field.getKey(), "", "field_read", at, measured));
            keys.put(field.getKey(), field.getValue().sourceId);
        }
        for (Map<String, Object> edge : edges) {
            if (!"call_return".equals(text(edge.get("kind")))) continue;
            String method = text(edge.get("method"));
            int unitIndex = MapFields.number(edge.get("unitIndex"), -1);
            ConfigRoots.Source source = config.call(method, unitIndex,
                    text(edge.get("invoke")));
            Integer at = cone.get(text(edge.get("toCell")));
            if (source == null || at == null) continue;
            String siteId = SiteId.render(method, unitIndex);
            sources.put(siteId, new Boundary(Kind.CONFIG_CALL,
                    text(edge.get("fromCell")), siteId, "call_return",
                    at + 1, measured));
            keys.put(siteId, source.sourceId);
        }
        return sources;
    }

    private static Map<String, Integer> keyDistances(
            Map<String, Boundary> sources, Map<String, String> keys) {
        Map<String, Integer> keyDistance = new TreeMap<>();
        for (Map.Entry<String, Boundary> source : sources.entrySet()) {
            keyDistance.merge(keys.get(source.getKey()),
                    source.getValue().distance, Math::min);
        }
        return keyDistance;
    }

    private static Set<String> nearest(Map<String, Boundary> sources,
                                       Map<String, String> keys,
                                       Set<String> taken) {
        Map<String, Integer> keyDistance = keyDistances(sources, keys);
        List<String> ordered = new ArrayList<>(keyDistance.keySet());
        ordered.sort(Comparator.comparingInt(keyDistance::get));
        Set<String> chosen = new LinkedHashSet<>();
        for (String key : ordered) {
            if (chosen.size() < WIDTH && keyDistance.get(key) <= DISTANCE
                    && !taken.contains(key)) {
                chosen.add(key);
            }
        }
        return chosen;
    }

    private static void choose(List<Boundary> found) {
        Map<Kind, Map<String, Integer>> cells = new HashMap<>();
        for (Boundary boundary : found) {
            if (boundary.kind == Kind.CUT) boundary.cut = DISTANCE_CUT;
            if (boundary.kind == Kind.CONFIG_FIELD
                    || boundary.kind == Kind.CONFIG_CALL
                    || boundary.kind == Kind.CUT
                    || boundary.kind == Kind.IO) {
                continue;
            }
            cells.computeIfAbsent(boundary.kind, ignored -> new TreeMap<>())
                    .merge(boundary.cell, boundary.distance, Math::min);
        }
        Map<Kind, Set<String>> chosen = new HashMap<>();
        for (Map.Entry<Kind, Map<String, Integer>> kind : cells.entrySet()) {
            List<String> ordered = new ArrayList<>(kind.getValue().keySet());
            ordered.sort(Comparator.comparingInt(kind.getValue()::get));
            chosen.put(kind.getKey(), new LinkedHashSet<>(ordered.subList(0,
                    Math.min(WIDTH, ordered.size()))));
        }
        for (Boundary boundary : found) {
            Set<String> nearest = chosen.get(boundary.kind);
            if (nearest != null) {
                boundary.chosen = nearest.contains(boundary.cell);
                boundary.cut = boundary.chosen ? "" : WIDTH_CUT;
            }
        }
    }

    private static final class Classifier {
        private final Map<String, List<Map<String, Object>>> into;
        private final Set<String> carried;
        private final Set<String> regionMethods;
        private final Set<String> roots;
        private final Map<String, Clock> clocks;
        private final ConfigRoots config;
        private final Function<String, SharedFieldFlow.TrackedKind>
                trackedKind;
        private final Predicate<String> constructionOnly;
        private final Predicate<String> systemClass;
        private final SystemView view = SystemView.current();

        Classifier(Map<String, List<Map<String, Object>>> into,
                   Set<String> carried, Set<String> regionMethods,
                   Set<String> roots, Map<String, Clock> clocks,
                   ConfigRoots config,
                   Function<String, SharedFieldFlow.TrackedKind> trackedKind,
                   Predicate<String> constructionOnly,
                   Predicate<String> systemClass) {
            this.into = into;
            this.carried = carried;
            this.regionMethods = regionMethods;
            this.roots = roots;
            this.clocks = clocks;
            this.config = config;
            this.trackedKind = trackedKind;
            this.constructionOnly = constructionOnly;
            this.systemClass = systemClass;
        }

        boolean follows(Map<String, Object> edge) {
            if (!RECEIVERS.contains(text(edge.get("kind")))) return true;
            String invoke = text(edge.get("invoke"));
            int colon = invoke.indexOf(':');
            return colon > 1 && VALUE_LIKE.matcher(invoke.substring(1,
                    colon)).matches();
        }

        Kind of(String cell, Map<String, Object> edge) {
            Matcher returned = RETURN.matcher(cell);
            if (returned.matches()) return returned(cell, returned.group(1));
            Matcher field = FIELD.matcher(cell);
            if (field.matches()) {
                return field(cell, field.group(1), field.group(2), edge);
            }
            Matcher formal = FORMAL.matcher(cell);
            if (formal.matches() && !into.containsKey(cell)) {
                return roots.contains(formal.group(1)) ? Kind.WIRE
                        : Kind.SCOPE;
            }
            return null;
        }

        private Kind returned(String cell, String callee) {
            if (clocks.containsKey(callee)) return Kind.CLOCK;
            if (config.callees().contains(callee)) return Kind.CONFIG_CALL;
            if (Debug.isBooleanMarkerSignature(callee)) return Kind.FAULT;
            if (LibraryCatalog.demandedDoor(callee) != null) return Kind.IO;
            if (into.containsKey(cell) || carried.contains(callee)) {
                return null;
            }
            String owner = callee.substring(1, callee.indexOf(':'));
            if (owner.startsWith(ATOMIC)) return Kind.READ;
            SootMethod method = CausynthStaticFacts.method(callee);
            if (IO.matcher(owner).matches()
                    || method != null && method.isNative()) {
                return Kind.IO;
            }
            if (JavaContainerTypes.shape(owner)
                    != JavaContainerTypes.Shape.NONE) {
                return Kind.TRACK_CONTAINER;
            }
            return CausynthStaticFacts.applicationMethod(callee)
                    || systemClass.test(owner) ? Kind.SCOPE : Kind.LIBRARY;
        }

        private Kind field(String cell, String owner, String type,
                           Map<String, Object> edge) {
            if (config.configField(cell)) return Kind.CONFIG_FIELD;
            if (owner.startsWith(ATOMIC) || type.startsWith(ATOMIC)) {
                return Kind.READ;
            }
            if (VALUE_LIKE.matcher(owner).matches()) return null;
            List<String> writers = new ArrayList<>();
            for (Map<String, Object> write : into.getOrDefault(cell,
                    Collections.<Map<String, Object>>emptyList())) {
                if (WRITES.contains(text(write.get("kind")))) {
                    writers.add(text(write.get("method")));
                }
            }
            if (writers.isEmpty() ? type.equals(owner) : constants(writers)) {
                return null;
            }
            boolean stored = false;
            boolean viewed = !writers.isEmpty();
            for (String writer : writers) {
                stored |= regionMethods.contains(writer);
                viewed &= view.holds(writer);
            }
            boolean container = JavaContainerTypes.shape(type)
                    != JavaContainerTypes.Shape.NONE;
            SharedFieldFlow.TrackedKind tracked = trackedKind.apply(cell);
            if (viewed && !container
                    && tracked != SharedFieldFlow.TrackedKind.VALUE) {
                stored = false;
            }
            if (constructionOnly.test(cell) && !container && (!stored
                    || tracked == SharedFieldFlow.TrackedKind.NONE)) {
                return Kind.PROVENANCE;
            }
            if (!stored) return Kind.PRE_WINDOW;
            if (container) return Kind.TRACK_CONTAINER;
            return tracked == SharedFieldFlow.TrackedKind.VALUE
                    ? Kind.TRACK : Kind.TRACK_IDENTITY;
        }

        private static boolean constants(Collection<String> writers) {
            for (String writer : writers) {
                if (!writer.endsWith(" <clinit>()>")) return false;
            }
            return true;
        }
    }
}
