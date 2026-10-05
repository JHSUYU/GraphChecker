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
 * chosen TRACK, TRACK_IDENTITY or TRACK_CONTAINER read is tracked though its
 * value takes more than the scope map's flows to a branch, a chosen READ is a
 * placeholder though only its own region stores it, a chosen SCOPE or
 * PRE_WINDOW boundary ranks first in scope growth ({@code
 * plan.ScopeFrontier}).  A configuration belongs to the world, read in
 * whichever occurrence wrote what the anchor reads, beyond the boundary
 * between them: its keys are measured on the whole cone (every edge, no
 * boundary stops it), and the {@value #WIDTH} nearest within {@value
 * #DISTANCE} are the ones minted; and measured again at the guards of the
 * writers of each chosen tracked read -- whether a writer ran decides what
 * the read saw -- where {@value #WIDTH} more are minted, so a key near a
 * writer never displaces one near the anchor.  {@value #FILE} beside the scope map lists
 * every boundary; the scope map's reads state their distance, the mark a
 * concrete anchor's demand keeps its reads by ({@code
 * explore.ClosurePlanner#concrete}).</p>
 *
 * <p>A local file operation is a fault door only where its result or its
 * failure flows into what the walk demanded ({@link Faults}, a demanded
 * door of the library catalog): (a) an IO boundary whose call returns a
 * failing result ({@code File#renameTo}'s false) into the path; (b) a call
 * whose fault, in the latent model ({@code FaultPropagation#latent}),
 * escapes its method before a demanded store (a writer of a chosen TRACK,
 * TRACK_IDENTITY, TRACK_CONTAINER or READ field), or goes to a handler that
 * decides a site the walk demanded -- a site on the target's path only when
 * the handler leads to it.  The {@value #WIDTH} nearest calls are chosen, the
 * doors already woven first ({@link DemandedDoors}), none whose demanded site
 * no region holds ({@value #NO_REGION_CUT}: a demanded door roots no region,
 * its marker is read where the site runs); a call into the system
 * outside the scope where such a fault could stand is an IO frontier row,
 * the {@value #WIDTH} nearest grown first.  Any other IO boundary is cut
 * {@value #NO_DOOR_CUT}.</p>
 */
final class RootDemand {
    /** The file beside the scope map. */
    static final String FILE = "root_demand.jsonl";
    /** The most edges a boundary may stand from the path guards. */
    static final int DISTANCE = 16;
    /** The most boundaries of one class chosen, nearest first. */
    static final int WIDTH = 12;

    /** A boundary's class; CUT is a path still open {@value #DISTANCE}
     *  edges out, no boundary: named, never chosen. */
    enum Kind {
        CLOCK, FAULT, CONFIG_CALL, CONFIG_FIELD, READ, TRACK, TRACK_IDENTITY,
        TRACK_CONTAINER, PRE_WINDOW, WIRE, IO, SCOPE, LIBRARY, CUT
    }

    /** Why a boundary is not chosen: past the {@value #WIDTH} nearest of
     *  its class, past {@value #DISTANCE} edges, or a configuration no
     *  source declares (a {@code String} getter): no root to mint. */
    static final String WIDTH_CUT = "WIDTH";
    static final String DISTANCE_CUT = "DISTANCE";
    static final String NO_SOURCE_CUT = "NO_SOURCE";
    /** An IO boundary no demanded door stands at: an observation, a
     *  stream not typed as a file's, a value its fault would not move. */
    static final String NO_DOOR_CUT = "NO_DOOR";
    /** A call whose demanded site no region holds: its marker would be
     *  read in no occurrence (a demanded door roots none). */
    static final String NO_REGION_CUT = "NO_REGION";
    /** How a door's outcome reaches the slice. */
    static final String VALUE = "VALUE";
    static final String ESCAPE = "ESCAPE";
    static final String HANDLER = "HANDLER";

    /**
     * Where a local file fault could stand on what the walk demanded: the
     * Soot side ({@link LatentFaults}).  Sites are this pass's site ids.
     */
    interface Faults {
        /** The demanded door with a failing result the call at {@code
         *  siteId} of {@code callee} would be, or null. */
        Candidate valued(String siteId, String callee);

        /**
         * The latent faults: those escaping before a store of {@code
         * stores}, and those a handler deciding a site of {@code demanded}
         * catches (one of {@code path} only where the handler leads to it),
         * each at its site's distance plus one plus the calls it escapes.
         */
        List<Candidate> latent(Map<String, Integer> demanded,
                               Map<String, Integer> stores,
                               Set<String> path);

        /** The site id of a woven door's call in this pass, or "". */
        String site(DemandedDoors.Site door);
    }

    /** One call where a door could stand, or, a frontier, a call into the
     *  system outside the scope where growing it could find one. */
    static final class Candidate {
        final String siteId;
        final String callee;
        final String caller;
        final int ordinal;
        final int distance;
        final String reach;
        final boolean frontier;
        /** The methods from the demanded site's down to the caller. */
        final List<String> via;
        /** Whether a region holds the demanded site's method, where the
         *  door's marker is read. */
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

    /** One boundary where one edge reaches it. */
    static final class Boundary {
        final Kind kind;
        final String cell;
        final String siteId;
        final String edgeKind;
        final int distance;
        boolean chosen;
        /** Why it is not chosen ({@link #WIDTH_CUT}, {@link
         *  #DISTANCE_CUT}, {@link #NO_SOURCE_CUT}), "" when it is. */
        String cut = "";
        /** A configuration's: measured from the path guards ({@link
         *  #PATH}) or from a tracked read's writers' guards ({@link
         *  #WRITERS}); every other boundary is the path's. */
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

    /** {@link Boundary#measured}: from the target's path guards. */
    static final String PATH = "PATH";
    /** {@link Boundary#measured}: from a chosen tracked read's writers'
     *  guards. */
    static final String WRITERS = "WRITERS";
    /** The demanded reads whose writers' guards a configuration is
     *  measured at. */
    private static final Set<Kind> TRACKED = java.util.EnumSet.of(Kind.TRACK,
            Kind.TRACK_IDENTITY, Kind.TRACK_CONTAINER, Kind.READ);

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
    /** The classes whose chosen fields' writers are demanded stores. */
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

    /**
     * @param regions     the region skeletons
     * @param clocks      the clock callees ({@link RootCatalog#clocks})
     * @param pathSites   the TARGET_SITE's guards, its chain and the chain's
     *                    deciders ({@code StaticScopeMap.Site#pathSites})
     * @param trackedKind how a replay versions a field
     * @param systemClass whether a class is the system's own
     * @param faults      where a local file fault could stand
     * @param woven       the demanded doors this pass wove
     */
    static RootDemand of(List<Map<String, Object>> edges,
                         List<Map<String, Object>> regions,
                         Map<String, Clock> clocks, ConfigRoots config,
                         Set<String> pathSites,
                         Function<String, SharedFieldFlow.TrackedKind>
                                 trackedKind,
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
            // A path guard's operand: the throw's own guards' and those of
            // the calls into its method (StaticScopeMap#targetChain).
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
                roots, clocks, config, trackedKind, systemClass);
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

    /**
     * The demanded doors: those {@code doors} holds (woven by this pass),
     * then the nearest calls whose failing result reaches the path (a) or
     * whose latent fault skips a demanded store or decides a demanded site
     * (b), up to {@value #WIDTH} in all, each added to {@code doors} and
     * listed as an IO boundary; any other IO boundary cut {@value
     * #NO_DOOR_CUT}.  Returns the IO frontier chosen: callee to distance.
     */
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

    /** A woven door's row: chosen, at the distance it was chosen at. */
    private static Boundary woven(DemandedDoors.Site door, String siteId) {
        Boundary boundary = new Boundary(Kind.IO, door.callee
                + FaultPropagation.THROWS, siteId, "door", door.distance);
        boundary.chosen = true;
        return boundary;
    }

    /** Every boundary, nearest first. */
    List<Boundary> boundaries() {
        return boundaries;
    }

    /** The demanded doors the next pass weaves ({@value
     *  DemandedDoors#FILE}): this pass's, then the ones it chose. */
    List<DemandedDoors.Site> doors() {
        return doors;
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
            row.addProperty("chosen", boundary.chosen);
            row.addProperty("cut", boundary.cut);
            row.addProperty("measured", boundary.measured);
            rows.add(row);
        }
        return rows;
    }

    /** What the scope map takes: the chosen TRACK and READ reads by site
     *  and cell, every boundary's distance. */
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

    /** The frontier signatures scope growth takes first, each with its
     *  class and distance: of the chosen boundaries, the callee of each
     *  SCOPE return, the method of each SCOPE formal, each PRE_WINDOW field
     *  (its writers may be out of scope), each IO frontier callee. */
    Map<String, StaticScopeMap.Demanded> frontier() {
        Map<String, StaticScopeMap.Demanded> frontier = new LinkedHashMap<>();
        for (Boundary boundary : boundaries) {
            if (!boundary.chosen) continue;
            Matcher returned = RETURN.matcher(boundary.cell);
            Matcher formal = FORMAL.matcher(boundary.cell);
            String signature = boundary.kind == Kind.PRE_WINDOW
                    ? boundary.cell
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

    /** Nearest first from the path guards' operands, every path stopped at
     *  its first boundary; {@code demanded} gets the site of every edge it
     *  followed, at the distance of the cell the edge comes from. */
    private static List<Boundary> walk(
            Map<String, List<Map<String, Object>>> into, Set<String> starts,
            Classifier classes, Map<String, Integer> demanded) {
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
            for (Map<String, Object> edge : into.getOrDefault(cell,
                    Collections.<Map<String, Object>>emptyList())) {
                if (!classes.follows(edge)) continue;
                // A path still open at the bound: cut here, named.
                if (next > DISTANCE) {
                    found.putIfAbsent(Kind.CUT + "\n" + cell, new Boundary(
                            Kind.CUT, cell, "", "", DISTANCE));
                    break;
                }
                String from = text(edge.get("fromCell"));
                String site = text(edge.get("siteId"));
                if (!site.isEmpty()) demanded.merge(site, next, Math::min);
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

    /** Each cell's distance on the whole cone: every edge, no boundary;
     *  the starts at 0. */
    private static Map<String, Integer> cone(
            Map<String, List<Map<String, Object>>> into, Set<String> starts) {
        Map<String, Integer> at = new LinkedHashMap<>();
        for (String start : starts) at.put(start, 0);
        return cone(into, at);
    }

    /** The cone from starts at their own distances. */
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

    /**
     * The operands of the guards of the writers of each chosen tracked read
     * (a store's own branches and those of the calls into its method: the
     * guard rows into the read's cell), each one edge past the read.
     */
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

    /**
     * The configuration boundaries, each source's at its distance on the
     * path guards' cone and on the writers' guards' -- a field's at the
     * field, a getter call's one past the local it lands in -- in place of
     * the walk's; and the keys chosen: the {@value #WIDTH} nearest within
     * {@value #DISTANCE} on the path's cone, and as many more on the
     * writers'.  A configuration the walk met that no source declares (a
     * {@code String} getter) stays as the walk found it, unchosen.
     */
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
                // A key not minted is named by why: past the bound, or past
                // the nearest WIDTH within it.
                boundary.cut = boundary.chosen ? ""
                        : keyDistance.get(key) > DISTANCE ? DISTANCE_CUT
                        : WIDTH_CUT;
                found.add(boundary);
            }
        }
        return chosen;
    }

    /** Each configuration source on one cone, by its field or its call
     *  site; its key into {@code keys}. */
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

    /** Each key's nearest source. */
    private static Map<String, Integer> keyDistances(
            Map<String, Boundary> sources, Map<String, String> keys) {
        Map<String, Integer> keyDistance = new TreeMap<>();
        for (Map.Entry<String, Boundary> source : sources.entrySet()) {
            keyDistance.merge(keys.get(source.getKey()),
                    source.getValue().distance, Math::min);
        }
        return keyDistance;
    }

    /** The {@value #WIDTH} nearest keys within {@value #DISTANCE} but the
     *  ones {@code taken}. */
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

    /** The {@value #WIDTH} nearest cells of each class the walk found are
     *  chosen; a configuration's choice is its key's. */
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
            if (config.callees().contains(callee)) return Kind.CONFIG_CALL;
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
