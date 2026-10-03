package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.annotation.Debug;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
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

/**
 * Where the values the declared throw's path guards decide on enter what the
 * slice can follow (SYMBOL-SCOPE §4.6): backward from the operands of the
 * TARGET_SITE's guards and chain over the candidate edges, nearest first,
 * every path stopped at its first BOUNDARY, at most {@value #DISTANCE} edges
 * out.  A boundary is one of
 * <ul>
 *   <li>a root: a clock's return (CLOCK), a fault marker's (FAULT), a
 *       configuration (CONFIG_CALL, CONFIG_FIELD, {@link ConfigRoots});</li>
 *   <li>shared state a replay re-pairs: an integral or boxed field a region
 *       stores (TRACK), a JDK atomic's value (READ);</li>
 *   <li>what no replay makes symbolic yet, named and never freed: a
 *       reference, {@code String} or enum field a region stores
 *       (TRACK_IDENTITY), a container's state (TRACK_CONTAINER), a field no
 *       region stores (PRE_WINDOW), a region root's formal (WIRE: the message
 *       or the thread start that hands it over), a file, stream, socket or
 *       native result (IO), a call into the system's own code outside the
 *       scope or a formal whose callers are (SCOPE), any other library
 *       result (LIBRARY).</li>
 * </ul>
 * Receiver edges name which object is read, not the value, and are followed
 * only to a value-like receiver (a box, a {@code String}).
 *
 * <p>Of each class the {@value #WIDTH} boundaries nearest are CHOSEN: a
 * chosen TRACK read is tracked though its value takes more than the scope
 * map's flows to a branch, a chosen READ is a placeholder though only its own
 * region stores it, a SCOPE or PRE_WINDOW boundary ranks first in scope
 * growth ({@code plan.ScopeFrontier}).  A configuration belongs to the world, read
 * in whichever occurrence wrote what the anchor reads, beyond the boundary
 * between them: its keys are measured on the whole cone (every edge, no
 * boundary stops it), and the {@value #WIDTH} nearest within {@value
 * #DISTANCE} are the ones minted.  {@value #FILE} beside the scope map lists
 * every boundary.</p>
 */
final class RootDemand {
    /** The file beside the scope map. */
    static final String FILE = "root_demand.jsonl";
    /** The most edges a boundary may stand from the path guards. */
    static final int DISTANCE = 16;
    /** The most boundaries of one class chosen, nearest first. */
    static final int WIDTH = 12;

    /** A boundary's class; the mintable ones are a replay's to fill. */
    enum Kind {
        CLOCK(true), FAULT(true), CONFIG_CALL(true), CONFIG_FIELD(true),
        READ(true), TRACK(true), TRACK_IDENTITY(false),
        TRACK_CONTAINER(false), PRE_WINDOW(false), WIRE(false), IO(false),
        SCOPE(false), LIBRARY(false);

        final boolean mintable;

        Kind(boolean mintable) {
            this.mintable = mintable;
        }
    }

    /** One boundary where one edge reaches it. */
    static final class Boundary {
        final Kind kind;
        final String cell;
        final String siteId;
        final String edgeKind;
        final int distance;
        boolean chosen;

        private Boundary(Kind kind, String cell, String siteId,
                         String edgeKind, int distance) {
            this.kind = kind;
            this.cell = cell;
            this.siteId = siteId;
            this.edgeKind = edgeKind;
            this.distance = distance;
        }
    }

    /** Edges that name which object is read rather than its value. */
    private static final Set<String> RECEIVERS = new LinkedHashSet<>(
            Arrays.asList("accessor_receiver", "method_receiver",
                    "constructor_receiver", "dispatch_receiver",
                    "dispatch_caller_receiver"));
    /** Edges that carry a call's operands to its result: a library return
     *  they reach is followed through them, no boundary. */
    private static final Set<String> OPERANDS = new LinkedHashSet<>(
            Arrays.asList("accessor_field_return", "local_def_use",
                    "container_receiver", "container_argument",
                    "library_receiver"));
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

    private RootDemand(List<Boundary> boundaries, Set<String> configSources) {
        this.boundaries = Collections.unmodifiableList(boundaries);
        this.configSources = Collections.unmodifiableSet(configSources);
    }

    /**
     * @param regions     the region skeletons
     * @param clocks      the clock callees ({@link RootCatalog#clocks})
     * @param pathSites   the TARGET_SITE's guards, its chain and the chain's
     *                    deciders ({@code StaticScopeMap.Site#pathSites})
     * @param trackedKind how a replay versions a field
     * @param systemClass whether a class is the system's own
     */
    static RootDemand of(List<Map<String, Object>> edges,
                         List<Map<String, Object>> regions,
                         Map<String, Clock> clocks, ConfigRoots config,
                         Set<String> pathSites,
                         Function<String, SharedFieldFlow.TrackedKind>
                                 trackedKind,
                         Predicate<String> systemClass) {
        Map<String, List<Map<String, Object>>> into = new HashMap<>();
        Set<String> carried = new LinkedHashSet<>();
        Set<String> starts = new LinkedHashSet<>();
        for (Map<String, Object> edge : edges) {
            into.computeIfAbsent(text(edge.get("toCell")),
                    ignored -> new ArrayList<>()).add(edge);
            if (OPERANDS.contains(text(edge.get("kind")))) {
                carried.add(text(edge.get("invoke")));
                carried.add(text(edge.get("accessorImplementationMethod")));
            }
            if ("exception_guard".equals(text(edge.get("kind")))
                    && pathSites.contains(text(edge.get("siteId")))) {
                starts.add(text(edge.get("fromCell")));
            }
        }
        Set<String> regionMethods = new LinkedHashSet<>();
        Set<String> roots = new LinkedHashSet<>();
        for (Map<String, Object> region : regions) {
            regionMethods.addAll(strings(region.get("methods")));
            roots.add(text(region.get("rootMethod")));
        }
        Classifier classes = new Classifier(into, carried, regionMethods,
                roots, clocks, config, trackedKind, systemClass);
        List<Boundary> found = walk(into, starts, classes);
        Map<String, Integer> cone = cone(into, starts);
        Set<String> chosenKeys = configuration(found, cone, config, edges);
        choose(found);
        found.sort(Comparator.comparingInt((Boundary b) -> b.distance)
                .thenComparing(b -> b.kind.name())
                .thenComparing(b -> b.cell).thenComparing(b -> b.siteId));
        return new RootDemand(found, chosenKeys);
    }

    /** Every boundary, nearest first. */
    List<Boundary> boundaries() {
        return boundaries;
    }

    /** The configuration roots chosen: the ones minted. */
    Set<String> configSources() {
        return configSources;
    }

    /** {@value #FILE}'s rows. */
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
            row.addProperty("mintable", boundary.kind.mintable);
            row.addProperty("chosen", boundary.chosen);
            rows.add(row);
        }
        return rows;
    }

    /** What the scope map takes: the chosen TRACK and READ reads by site
     *  and cell, every boundary's distance. */
    StaticScopeMap.Demand marks() {
        Map<String, Boundary> nearest = new LinkedHashMap<>();
        for (Boundary boundary : boundaries) {
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

    /** The frontier signatures scope growth takes first, each with its
     *  class: the callee of each SCOPE return, the method of each SCOPE
     *  formal, each PRE_WINDOW field (its writers may be out of scope). */
    Map<String, String> frontier() {
        Map<String, String> frontier = new LinkedHashMap<>();
        for (Boundary boundary : boundaries) {
            Matcher returned = RETURN.matcher(boundary.cell);
            Matcher formal = FORMAL.matcher(boundary.cell);
            String signature = boundary.kind == Kind.PRE_WINDOW
                    ? boundary.cell
                    : boundary.kind != Kind.SCOPE ? null
                    : returned.matches() ? returned.group(1)
                    : formal.matches() ? formal.group(1) : null;
            if (signature != null) {
                frontier.putIfAbsent(signature, boundary.kind.name());
            }
        }
        return frontier;
    }

    /** Nearest first from the path guards' operands, every path stopped at
     *  its first boundary. */
    private static List<Boundary> walk(
            Map<String, List<Map<String, Object>>> into, Set<String> starts,
            Classifier classes) {
        Map<String, Integer> distance = new HashMap<>();
        Map<String, Boundary> found = new LinkedHashMap<>();
        Deque<String> queue = new ArrayDeque<>();
        for (String start : starts) {
            distance.put(start, 0);
            queue.add(start);
        }
        while (!queue.isEmpty()) {
            String cell = queue.removeFirst();
            int next = distance.get(cell) + 1;
            if (next > DISTANCE) continue;
            for (Map<String, Object> edge : into.getOrDefault(cell,
                    Collections.<Map<String, Object>>emptyList())) {
                if (!classes.follows(edge)) continue;
                String from = text(edge.get("fromCell"));
                Kind kind = classes.of(from, edge);
                if (kind != null) {
                    String siteId = text(edge.get("siteId"));
                    found.putIfAbsent(kind + "\n" + from + "\n" + siteId,
                            new Boundary(kind, from, siteId,
                                    text(edge.get("kind")), next));
                    continue;
                }
                if (distance.putIfAbsent(from, next) == null) {
                    queue.addLast(from);
                }
            }
        }
        return new ArrayList<>(found.values());
    }

    /** Each cell's distance on the whole cone: every edge, no boundary. */
    private static Map<String, Integer> cone(
            Map<String, List<Map<String, Object>>> into, Set<String> starts) {
        Map<String, Integer> distance = new HashMap<>();
        Deque<String> queue = new ArrayDeque<>();
        for (String start : starts) {
            distance.put(start, 0);
            queue.add(start);
        }
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

    /**
     * The configuration boundaries, each source's at its cone distance --
     * a field's at the field, a getter call's one past the local it lands
     * in -- in place of the walk's; and the {@value #WIDTH} keys nearest
     * within {@value #DISTANCE}, the ones chosen.  A configuration the walk
     * met that no source declares (a {@code String} getter) stays as the
     * walk found it, unchosen.
     */
    private static Set<String> configuration(
            List<Boundary> found, Map<String, Integer> cone,
            ConfigRoots config, List<Map<String, Object>> edges) {
        Map<String, Boundary> sources = new LinkedHashMap<>();
        Map<String, String> keys = new HashMap<>();
        for (Map.Entry<String, ConfigRoots.Source> field
                : config.fields().entrySet()) {
            Integer at = cone.get(field.getKey());
            if (at == null) continue;
            sources.put(field.getKey(), new Boundary(Kind.CONFIG_FIELD,
                    field.getKey(), "", "field_read", at));
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
                    at + 1));
            keys.put(siteId, source.sourceId);
        }
        Map<String, Integer> keyDistance = new TreeMap<>();
        for (Map.Entry<String, Boundary> source : sources.entrySet()) {
            keyDistance.merge(keys.get(source.getKey()),
                    source.getValue().distance, Math::min);
        }
        List<String> ordered = new ArrayList<>(keyDistance.keySet());
        ordered.sort(Comparator.comparingInt(keyDistance::get));
        Set<String> chosen = new LinkedHashSet<>();
        for (String key : ordered) {
            if (chosen.size() < WIDTH && keyDistance.get(key) <= DISTANCE) {
                chosen.add(key);
            }
        }
        found.removeIf(boundary -> (boundary.kind == Kind.CONFIG_FIELD
                || boundary.kind == Kind.CONFIG_CALL)
                && (sources.containsKey(boundary.cell)
                || sources.containsKey(boundary.siteId)));
        for (Map.Entry<String, Boundary> source : sources.entrySet()) {
            Boundary boundary = source.getValue();
            boundary.chosen = chosen.contains(keys.get(source.getKey()));
            found.add(boundary);
        }
        return chosen;
    }

    /** The {@value #WIDTH} nearest cells of each mintable class the walk
     *  found are chosen; a configuration's choice is its key's. */
    private static void choose(List<Boundary> found) {
        Map<Kind, Map<String, Integer>> cells = new HashMap<>();
        for (Boundary boundary : found) {
            if (!boundary.kind.mintable || boundary.kind == Kind.CONFIG_FIELD
                    || boundary.kind == Kind.CONFIG_CALL) {
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
            }
        }
    }

    /** Which class a cell reached by an edge is, or null to go on. */
    private static final class Classifier {
        private final Map<String, List<Map<String, Object>>> into;
        private final Set<String> carried;
        private final Set<String> regionMethods;
        private final Set<String> roots;
        private final Map<String, Clock> clocks;
        private final ConfigRoots config;
        private final Function<String, SharedFieldFlow.TrackedKind>
                trackedKind;
        private final Predicate<String> systemClass;

        Classifier(Map<String, List<Map<String, Object>>> into,
                   Set<String> carried, Set<String> regionMethods,
                   Set<String> roots, Map<String, Clock> clocks,
                   ConfigRoots config,
                   Function<String, SharedFieldFlow.TrackedKind> trackedKind,
                   Predicate<String> systemClass) {
            this.into = into;
            this.carried = carried;
            this.regionMethods = regionMethods;
            this.roots = roots;
            this.clocks = clocks;
            this.config = config;
            this.trackedKind = trackedKind;
            this.systemClass = systemClass;
        }

        /** A receiver edge only to a value-like receiver. */
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
            if (config.configCallee(callee)) return Kind.CONFIG_CALL;
            if (Debug.isBooleanMarkerSignature(callee)) return Kind.FAULT;
            // An expanded body, or the call's operand edges, carry it.
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
            // A box's or a String's own state: its receiver carries it.
            if (VALUE_LIKE.matcher(owner).matches()) return null;
            List<String> writers = new ArrayList<>();
            for (Map<String, Object> write : into.getOrDefault(cell,
                    Collections.<Map<String, Object>>emptyList())) {
                if (WRITES.contains(text(write.get("kind")))) {
                    writers.add(text(write.get("method")));
                }
            }
            if (writers.isEmpty() ? type.equals(owner) : constants(writers)) {
                // A class's constant: written only in <clinit>, or an enum
                // constant of its own type.
                return null;
            }
            boolean stored = false;
            for (String writer : writers) {
                stored |= regionMethods.contains(writer);
            }
            if (!stored) return Kind.PRE_WINDOW;
            if (JavaContainerTypes.shape(type)
                    != JavaContainerTypes.Shape.NONE) {
                return Kind.TRACK_CONTAINER;
            }
            return trackedKind.apply(cell) == SharedFieldFlow.TrackedKind.VALUE
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
