package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.annotation.Debug;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What the static slice knows about the sites the target's demand can reach:
 * one artifact, one row shape (CLOSURE-V2 SS4). The demand is dynamic, so this
 * side publishes only what program text states; exploration joins the two.
 *
 * <ul>
 *   <li>{@code WRITE_SITE}: a store into a declared field the slice names,
 *       with its {@code carrier} field, versioned leaf {@code cell} and region
 *       (generalises REPORT-P2N's {@code observedWriteSites} to every cell of
 *       the slice).</li>
 *   <li>{@code EXPORT_SITE}: defines the value of a declared wire port
 *       ({@code portId}), the producer half of an interaction.</li>
 *   <li>{@code DECLARED_SITE}: a value entering from outside the slice's
 *       text that a case may declare symbolic -- an {@code ACCESSOR_RETURN} or
 *       a {@code CALL_RETURN} (incl. {@code Debug.makeSymbolicBoolean} fault
 *       markers) -- with the static half of the port it would mint ({@link
 *       Declared}). Scope only: {@code ConcolicScheduler
 *       .SymbolicInputSelection} alone decides admission.</li>
 *   <li>{@code TARGET_SITE}: the annotated throw the slice starts at.</li>
 *   <li>{@code ROOT_SITE}: each reached call site defining a {@code
 *       <callee>.return} cell, with the {@code local} it lands in (where
 *       INSTRUMENT binds a {@code LOCAL_DEFINITION}). It names its region by
 *       {@link #holders}, so a mint address is the same in seed and
 *       replay.</li>
 * </ul>
 *
 * <p>Every row carries {@code guards}: the branch sites it is control-dependent
 * on by post-dominance (CLOSURE-V2 SS1), i.e. what exploration may flip;
 * computed where Soot is, supplied via {@link Guards}.</p>
 *
 * <p>Scoping only: never what a site wrote, a port carried, or which occurrence
 * ran.</p>
 */
public final class StaticScopeMap {
    public static final String FILE = "static_scope_map.jsonl";
    public static final String SITE_KIND = "STATIC_SCOPE_SITE";
    public static final int SCHEMA_VERSION = 1;

    public static final String WRITE_SITE = "WRITE_SITE";
    public static final String EXPORT_SITE = "EXPORT_SITE";
    public static final String TARGET_SITE = "TARGET_SITE";
    public static final String ROOT_SITE = "ROOT_SITE";
    public static final String DECLARED_SITE = "DECLARED_SITE";

    /** {@code declaredKind}: a field accessor's return; its cell is the field.
     */
    public static final String ACCESSOR_RETURN = "ACCESSOR_RETURN";
    /** {@code declaredKind}: an external call's return; its cell is {@code
     *  <callee>.return}. */
    public static final String CALL_RETURN = "CALL_RETURN";

    /** A Jimple local cell: {@code <method>::local[#suffix]}. */
    private static final java.util.regex.Pattern LOCAL_CELL =
            java.util.regex.Pattern.compile("^(<.+>)::([^#]+)(?:#.*)?$");

    private static final String[] WRITE_KINDS = {"field_write",
            "field_mutation", "container_mutation_argument",
            "container_call_mutation_effect", "container_array_store_value"};
    private static final String THROW_KIND = "exception_throw";

    /** The guard set of one site, asked of the stage that has the CFG. */
    public interface Guards {
        /** The branches {@code siteId} is control-dependent on. */
        List<Guard> of(String siteId);
    }

    /** One branch a site is control-dependent on, with the arm that reaches it
     *  (for the annotated throw, the fatal polarity). {@code null} outcome: not
     *  binary (a switch). */
    public static final class Guard {
        private final String siteId;
        private final Boolean outcome;

        public Guard(String siteId, Boolean outcome) {
            this.siteId = siteId == null ? "" : siteId;
            this.outcome = outcome;
        }

        public String siteId() {
            return siteId;
        }

        public Boolean outcome() {
            return outcome;
        }

        @Override
        public String toString() {
            return siteId + "=" + outcome;
        }
    }

    /** One site the static slice names, and what it is about. */
    public static final class Site {
        public final String role;
        public final String regionId;
        public final String siteId;
        /** The method half of the site as the VM spells it. */
        public final String vmSite;
        /** WRITE_SITE: the leaf the VM versions. */
        public final String cell;
        /** The declared field that owns {@link #cell}. */
        public final String carrier;
        public final String portId;
        /** WRITE_SITE: the callee that performs the store. */
        public final String declaredCallee;
        /** ROOT_SITE: the local the value lands in. */
        public final String local;
        /** DECLARED_SITE's static half; null otherwise. */
        public final Declared declared;
        public final List<String> guards;
        /** Arm of each {@link #guards} entry reaching this site; null if not
         *  binary. */
        public final List<Boolean> guardOutcomes;

        Site(String role, String regionId, String siteId, String vmSite,
             String cell, String carrier, String portId,
             String declaredCallee, String local,
             List<String> guards, List<Boolean> guardOutcomes) {
            this(role, regionId, siteId, vmSite, cell, carrier, portId,
                    declaredCallee, local, null, guards, guardOutcomes);
        }

        Site(String role, String regionId, String siteId, String vmSite,
             String cell, String carrier, String portId,
             String declaredCallee, String local, Declared declared,
             List<String> guards, List<Boolean> guardOutcomes) {
            this.declared = declared;
            this.role = role;
            this.regionId = regionId;
            this.siteId = siteId;
            this.vmSite = vmSite;
            this.cell = cell;
            this.carrier = carrier;
            this.portId = portId;
            this.declaredCallee = declaredCallee;
            this.local = local;
            this.guards = Collections.unmodifiableList(
                    new ArrayList<String>(guards));
            this.guardOutcomes = Collections.unmodifiableList(
                    new ArrayList<Boolean>(guardOutcomes));
        }

        Site withGuards(List<Guard> found) {
            List<String> sites = new ArrayList<String>();
            List<Boolean> outcomes = new ArrayList<Boolean>();
            for (Guard guard : found) {
                sites.add(guard.siteId());
                outcomes.add(guard.outcome());
            }
            return new Site(role, regionId, siteId, vmSite, cell, carrier,
                    portId, declaredCallee, local, declared, sites,
                    outcomes);
        }

        /** The arm of {@code guardSiteId} that reaches this site, or null. */
        public Boolean outcomeOf(String guardSiteId) {
            for (int index = 0; index < guards.size(); index++) {
                if (guards.get(index).equals(guardSiteId)) {
                    return guardOutcomes.size() > index
                            ? guardOutcomes.get(index) : null;
                }
            }
            return null;
        }

        @Override
        public String toString() {
            return role + " " + regionId + " " + siteId;
        }
    }

    /** The static half of one DECLARED_SITE, read off its candidate edge. */
    public static final class Declared {
        public final String kind;
        public final String edgeId;
        /** The cell the value lands in (the edge's {@code toCell}). */
        public final String dependencyCell;
        /** For an accessor: the method that answers the call. */
        public final String implementationMethod;
        public final String javaType;

        public Declared(String kind, String edgeId, String dependencyCell,
                        String implementationMethod, String javaType) {
            this.kind = safe(kind);
            this.edgeId = safe(edgeId);
            this.dependencyCell = safe(dependencyCell);
            this.implementationMethod = safe(implementationMethod);
            this.javaType = safe(javaType);
        }

        private static String safe(String value) {
            return value == null ? "" : value;
        }
    }

    /** Region skeletons, published beside {@link #FILE}. */
    public static final String REGIONS = "region_skeletons.jsonl";

    private final List<Site> sites;
    /** Method set of each retained region: the reverse of {@link #holders}.
     *  Needed because under the fold rule a site of region R is recorded under
     *  an enclosing R' ({@code explore.ClosurePlanner#candidates}), which
     *  region-id equality cannot see. Empty when skeletons were absent. */
    private final Map<String, Set<String>> regionMethods;

    private StaticScopeMap(List<Site> sites) {
        this(sites, Collections.<String, Set<String>>emptyMap());
    }

    private StaticScopeMap(List<Site> sites,
                           Map<String, Set<String>> regionMethods) {
        this.sites = Collections.unmodifiableList(sites);
        this.regionMethods = Collections.unmodifiableMap(regionMethods);
    }

    /** Methods one retained region holds; empty means "cannot say" (no
     *  skeletons), never "holds nothing" -- callers then fall back to comparing
     *  region ids. */
    public Set<String> methodsOf(String regionId) {
        Set<String> methods = regionMethods.get(
                regionId == null ? "" : regionId);
        return methods == null ? Collections.<String>emptySet() : methods;
    }

    // ---- building (PLAN) ----------------------------------------------

    /**
     * Every site the slice names, before guards are computed.
     *
     * @param edges   the candidate graph's rows
     * @param regions region skeletons: {@code regionId}, {@code methods}, ports
     */
    public static List<Site> sites(List<Map<String, Object>> edges,
                                   List<Map<String, Object>> regions) {
        return sites(edges, regions,
                DeclaredSymbolicInputs.configuredCallees().keySet());
    }

    /**
     * As above with the declared callees stated.
     *
     * @param declaredCallees the case's declared
     *                        callees; they bound the {@code CALL_RETURN} rows
     *                        (only a named callee can be a root). {@code
     *                        ACCESSOR_RETURN} rows are bounded by edge kind and
     *                        published whole.
     */
    public static List<Site> sites(List<Map<String, Object>> edges,
                                   List<Map<String, Object>> regions,
                                   Collection<String> declaredCallees) {
        Set<String> callees = new LinkedHashSet<String>(
                declaredCallees == null
                        ? Collections.<String>emptySet() : declaredCallees);
        List<Region> retained = regions(regions);
        Set<String> regionRoots = new LinkedHashSet<String>();
        for (Region region : retained) regionRoots.addAll(region.methods);
        List<Site> found = new ArrayList<Site>();
        Set<String> seen = new LinkedHashSet<String>();
        for (Map<String, Object> edge : edges == null
                ? Collections.<Map<String, Object>>emptyList() : edges) {
            String kind = text(edge.get("kind"));
            String method = text(edge.get("method"));
            int unitIndex = integer(edge.get("unitIndex"));
            if (method.isEmpty() || unitIndex < 0) continue;
            if (THROW_KIND.equals(kind)) {
                add(found, seen, retained, TARGET_SITE, method, unitIndex,
                        "", "", "", "");
                continue;
            }
            addRootSite(found, seen, retained, edge, method, unitIndex);
            addDeclaredSite(found, seen, retained, edge, kind, method,
                    unitIndex, callees, regionRoots);
            if (!write(kind)) continue;
            String carrier = signature(text(edge.get("toCell")));
            if (carrier.isEmpty()) continue;
            String invoke = text(edge.get("invoke"));
            String leaf = SharedFieldFlow.atomicValueField(carrier, invoke);
            add(found, seen, retained, WRITE_SITE, method, unitIndex,
                    leaf.isEmpty() ? carrier : leaf, carrier, "", invoke);
        }
        for (Region region : retained) {
            for (Map<String, Object> port : region.ports) {
                String portId = text(port.get(
                        CommunicationCatalogContract.PORT_ID));
                String method = text(port.get(CommunicationCatalogContract
                        .PORT_DEFINITION_METHOD));
                if (portId.isEmpty() || method.isEmpty()) continue;
                int unitIndex = integer(port.get(CommunicationCatalogContract
                        .PORT_DEFINITION_UNIT_INDEX));
                String siteId = unitIndex < 0 ? method
                        : SiteId.of(method, unitIndex);
                if (!seen.add(EXPORT_SITE + "|" + region.regionId + "|"
                        + siteId + "|" + portId)) {
                    continue;
                }
                found.add(new Site(EXPORT_SITE, region.regionId, siteId,
                        vmSite(method), "", "", portId, "", "",
                        Collections.<String>emptyList(),
                        Collections.<Boolean>emptyList()));
            }
        }
        return found;
    }

    /** Every site id in {@code sites}. */
    public static Set<String> siteIds(Collection<Site> sites) {
        Set<String> ids = new LinkedHashSet<String>();
        for (Site site : sites) ids.add(site.siteId);
        return ids;
    }

    /** The artifact's rows: one per site. */
    public static List<JsonObject> rows(List<Site> sites, Guards guards) {
        List<JsonObject> rows = new ArrayList<JsonObject>();
        for (Site site : sites) {
            List<Guard> found = guards == null
                    ? Collections.<Guard>emptyList()
                    : guards.of(site.siteId);
            rows.add(row(site.withGuards(found == null
                    ? Collections.<Guard>emptyList() : found)));
        }
        return rows;
    }

    private static JsonObject row(Site site) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", SCHEMA_VERSION);
        row.addProperty("kind", SITE_KIND);
        row.addProperty("role", site.role);
        row.addProperty("regionId", site.regionId);
        row.addProperty("siteId", site.siteId);
        row.addProperty("vmSite", site.vmSite);
        row.addProperty("cell", site.cell);
        row.addProperty("carrier", site.carrier);
        row.addProperty("portId", site.portId);
        if (!site.declaredCallee.isEmpty()) {
            row.addProperty("declaredCallee", site.declaredCallee);
        }
        if (!site.local.isEmpty()) {
            row.addProperty("local", site.local);
        }
        if (site.declared != null) {
            row.addProperty("declaredKind", site.declared.kind);
            row.addProperty("edgeId", site.declared.edgeId);
            row.addProperty("dependencyCell", site.declared.dependencyCell);
            row.addProperty("javaType", site.declared.javaType);
            if (!site.declared.implementationMethod.isEmpty()) {
                row.addProperty("implementationMethod",
                        site.declared.implementationMethod);
            }
        }
        JsonArray guards = new JsonArray();
        for (String guard : site.guards) guards.add(guard);
        row.add("guards", guards);
        if (!site.guards.isEmpty()) {
            JsonArray outcomes = new JsonArray();
            for (int index = 0; index < site.guards.size(); index++) {
                Boolean outcome = site.guardOutcomes.size() > index
                        ? site.guardOutcomes.get(index) : null;
                if (outcome == null) {
                    outcomes.add(JsonNull.INSTANCE);
                } else {
                    outcomes.add(outcome);
                }
            }
            row.add("guardOutcomes", outcomes);
        }
        return row;
    }

    /** ROOT_SITE rows of an edge defining a local of its own method from a
     *  {@code <callee>.return} cell. */
    private static void addRootSite(List<Site> into, Set<String> seen,
                                    List<Region> retained,
                                    Map<String, Object> edge, String method,
                                    int unitIndex) {
        if (!Boolean.TRUE.equals(edge.get("definitionSite"))) return;
        String source = text(edge.get("fromCell"));
        if (!source.contains(">.return")) return;
        java.util.regex.Matcher local = LOCAL_CELL.matcher(
                text(edge.get("toCell")));
        if (!local.matches() || !local.group(1).equals(method)) return;
        String siteId = SiteId.of(method, unitIndex);
        // One row per innermost holding region (never choose between siblings);
        // a method no region holds is published once with region "".
        List<String> owners = new ArrayList<String>(
                holders(retained, method));
        if (owners.isEmpty()) owners.add("");
        for (String regionId : owners) {
            if (!seen.add(ROOT_SITE + "|" + regionId + "|" + siteId + "|"
                    + source + "|" + local.group(2))) {
                continue;
            }
            into.add(new Site(ROOT_SITE, regionId, siteId, vmSite(method),
                    source, "", "", "", local.group(2),
                    Collections.<String>emptyList(),
                    Collections.<Boolean>emptyList()));
        }
    }

    /** DECLARED_SITE rows of one candidate edge producing a value from outside
     *  the slice's text: {@code accessor_field_return} (cell = the field);
     *  {@code call_return} of a declared callee no region holds (a region
     *  callee already publishes rows; two authorities for one value is the
     *  trap); and {@code explicit_symbolic_fault}, the workload's fault marker.
     */
    private static void addDeclaredSite(
            List<Site> into, Set<String> seen, List<Region> retained,
            Map<String, Object> edge, String kind, String method,
            int unitIndex, Set<String> declaredCallees,
            Set<String> regionMethods) {
        String callee = text(edge.get("invoke"));
        if (callee.isEmpty()) return;
        String cell;
        String implementation = "";
        if ("accessor_field_return".equals(kind)) {
            cell = firstNonEmpty(text(edge.get("declaredFieldSignature")),
                    text(edge.get("fromCell")));
            implementation = text(edge.get("accessorImplementationMethod"));
            if (implementation.isEmpty()) return;
        } else if ("call_return".equals(kind)
                && declaredCallees.contains(callee)
                && !regionMethods.contains(callee)
                || "explicit_symbolic_fault".equals(kind)
                && Debug.isBooleanMarkerSignature(callee)
                && declaredFault(text(edge.get("symbolicName")))) {
            cell = text(edge.get("fromCell"));
        } else {
            return;
        }
        String javaType = declaredType(cell, callee, kind);
        if (cell.isEmpty() || javaType.isEmpty()) return;
        String dependencyCell = text(edge.get("toCell"));
        if (dependencyCell.isEmpty()) return;
        String declaredKind = "accessor_field_return".equals(kind)
                ? ACCESSOR_RETURN : CALL_RETURN;
        String siteId = SiteId.of(method, unitIndex);
        List<String> owners = new ArrayList<String>(
                holders(retained, method));
        if (owners.isEmpty()) owners.add("");
        for (String regionId : owners) {
            if (!seen.add(DECLARED_SITE + "|" + regionId + "|" + siteId
                    + "|" + cell + "|" + callee + "|" + dependencyCell)) {
                continue;
            }
            into.add(new Site(DECLARED_SITE, regionId, siteId,
                    vmSite(method), cell, "", "", callee, "",
                    new Declared(declaredKind, text(edge.get("id")),
                            dependencyCell, implementation, javaType),
                    Collections.<String>emptyList(),
                    Collections.<Boolean>emptyList()));
        }
    }

    /** Whether a marker is a case fault point: a door fault ({@code
     *  FAULT:<TRANSPORT>:<DIRECTION>}) on a mapped transport; any other name is
     *  the workload's own declaration. */
    static boolean declaredFault(String name) {
        if (!name.startsWith("FAULT:")) return true;
        String[] parts = name.split(":", -1);
        return parts.length >= 2 && edu.uva.liftlab.graphchecker.causynth
                .WireFlowCatalog.declaredTransports().contains(parts[1]);
    }

    /** Primitive type of a declared site's value (field or callee return), else
     *  "". */
    private static String declaredType(String cell, String callee,
                                       String kind) {
        String signature = "accessor_field_return".equals(kind)
                ? cell : callee;
        int colon = signature.indexOf(": ");
        if (!signature.startsWith("<") || colon < 0) return "";
        String rest = signature.substring(colon + 2).trim();
        int space = rest.indexOf(' ');
        if (space <= 0) return "";
        String type = rest.substring(0, space);
        return PRIMITIVE_TYPES.contains(type) ? type : "";
    }

    private static final Set<String> PRIMITIVE_TYPES =
            Collections.unmodifiableSet(new LinkedHashSet<String>(
                    java.util.Arrays.asList("boolean", "byte", "char",
                            "short", "int", "long", "float", "double")));

    private static String firstNonEmpty(String first, String second) {
        return first == null || first.isEmpty()
                ? (second == null ? "" : second) : first;
    }

    private static void add(List<Site> into, Set<String> seen,
                            List<Region> retained, String role, String method,
                            int unitIndex, String cell, String carrier,
                            String portId, String declaredCallee) {
        String siteId = SiteId.of(method, unitIndex);
        for (String regionId : holders(retained, method)) {
            if (!seen.add(role + "|" + regionId + "|" + siteId + "|"
                    + carrier)) {
                continue;
            }
            into.add(new Site(role, regionId, siteId, vmSite(method), cell,
                    carrier, portId, declaredCallee, "",
                    Collections.<String>emptyList(),
                    Collections.<Boolean>emptyList()));
        }
    }

    private static boolean write(String kind) {
        for (String write : WRITE_KINDS) {
            if (write.equals(kind)) return true;
        }
        return false;
    }

    private static final class Region {
        private final String regionId;
        private final Set<String> methods;
        private final List<Map<String, Object>> ports;

        private Region(String regionId, Set<String> methods,
                       List<Map<String, Object>> ports) {
            this.regionId = regionId;
            this.methods = methods;
            this.ports = ports;
        }
    }

    @SuppressWarnings("unchecked")
    private static List<Region> regions(List<Map<String, Object>> rows) {
        List<Region> regions = new ArrayList<Region>();
        for (Map<String, Object> row : rows == null
                ? Collections.<Map<String, Object>>emptyList() : rows) {
            String regionId = text(row.get("regionId"));
            if (regionId.isEmpty()) continue;
            Set<String> methods = new LinkedHashSet<String>();
            for (Object method : list(row.get("methods"))) {
                String name = text(method);
                if (!name.isEmpty()) methods.add(name);
            }
            List<Map<String, Object>> ports =
                    new ArrayList<Map<String, Object>>();
            for (Object port : list(row.get("communicationPorts"))) {
                if (port instanceof Map) {
                    ports.add((Map<String, Object>) port);
                }
            }
            regions.add(new Region(regionId, methods, ports));
        }
        return regions;
    }

    /** The INNERMOST retained regions holding one method. The recording
     *  attributes an event to the innermost activation, so an enclosing region
     *  would name every occurrence of the request as a writer. Innermost is set
     *  inclusion, not a ranking; incomparable regions are all returned. */
    private static List<String> holders(List<Region> retained, String method) {
        List<Region> holding = new ArrayList<Region>();
        for (Region region : retained) {
            if (region.methods.contains(method)) holding.add(region);
        }
        List<String> innermost = new ArrayList<String>();
        for (Region region : holding) {
            boolean encloses = false;
            for (Region other : holding) {
                if (other == region) continue;
                if (region.methods.containsAll(other.methods)
                        && other.methods.size() < region.methods.size()) {
                    encloses = true;
                    break;
                }
            }
            if (!encloses) innermost.add(region.regionId);
        }
        return innermost;
    }

    // ---- reading and joining (EXPLORE) --------------------------------

    /** The published map, or empty when the epoch published none. */
    public static StaticScopeMap read(Path file) throws IOException {
        if (file == null || !Files.isRegularFile(file)) return empty();
        List<Site> sites = new ArrayList<Site>();
        for (JsonObject row : ArtifactIO.readJsonl(file)) {
            if (!SITE_KIND.equals(string(row, "kind"))) continue;
            List<String> guards = new ArrayList<String>();
            JsonElement stated = row.get("guards");
            if (stated != null && stated.isJsonArray()) {
                for (JsonElement guard : stated.getAsJsonArray()) {
                    guards.add(guard.getAsString());
                }
            }
            List<Boolean> outcomes = new ArrayList<Boolean>();
            JsonElement statedOutcomes = row.get("guardOutcomes");
            if (statedOutcomes != null && statedOutcomes.isJsonArray()) {
                for (JsonElement outcome : statedOutcomes.getAsJsonArray()) {
                    outcomes.add(outcome == null || outcome.isJsonNull()
                            ? null : Boolean.valueOf(outcome.getAsBoolean()));
                }
            }
            String declaredKind = string(row, "declaredKind");
            Declared declared = declaredKind.isEmpty() ? null
                    : new Declared(declaredKind, string(row, "edgeId"),
                            string(row, "dependencyCell"),
                            string(row, "implementationMethod"),
                            string(row, "javaType"));
            sites.add(new Site(string(row, "role"), string(row, "regionId"),
                    string(row, "siteId"), string(row, "vmSite"),
                    string(row, "cell"), string(row, "carrier"),
                    string(row, "portId"), string(row, "declaredCallee"),
                    string(row, "local"), declared, guards, outcomes));
        }
        return new StaticScopeMap(sites, readRegions(file));
    }

    /** Region method sets from the skeletons PLAN wrote beside the map (plain
     *  or gzipped). None beside it: empty, and the join falls back to region
     *  ids. */
    private static Map<String, Set<String>> readRegions(Path map) {
        Path beside = map.toAbsolutePath().getParent();
        if (beside == null) return Collections.emptyMap();
        Map<String, Set<String>> methods =
                new LinkedHashMap<String, Set<String>>();
        for (String name : new String[]{REGIONS, REGIONS + ".gz"}) {
            Path file = beside.resolve(name);
            if (!Files.isRegularFile(file)) continue;
            try {
                for (JsonObject row : ArtifactIO.readJsonl(file)) {
                    String regionId = string(row, "regionId");
                    if (regionId.isEmpty()) continue;
                    Set<String> held = new LinkedHashSet<String>();
                    JsonElement stated = row.get("methods");
                    if (stated != null && stated.isJsonArray()) {
                        for (JsonElement method : stated.getAsJsonArray()) {
                            held.add(method.getAsString());
                        }
                    }
                    methods.put(regionId, Collections.unmodifiableSet(held));
                }
            } catch (IOException | RuntimeException unreadable) {
                // Present but unreadable is a PLAN defect, refused by name.
                throw new IllegalStateException(
                        "REGION_SKELETONS_UNREADABLE: " + file, unreadable);
            }
            break;
        }
        return methods;
    }

    /** No map: every join answers nothing. */
    public static StaticScopeMap empty() {
        return new StaticScopeMap(new ArrayList<Site>());
    }

    public boolean stated() {
        return !sites.isEmpty();
    }

    /** The carriers the slice says one RECORDED write site stores into, joined
     *  on the shared method (VM vs Soot spellings) plus the type, when stated.
     */
    public Set<String> carriersAt(String recordedSite, String javaType) {
        Set<String> carriers = new LinkedHashSet<String>();
        String site = recordedSite == null ? "" : recordedSite;
        for (Site named : sites) {
            if (!WRITE_SITE.equals(named.role) || named.carrier.isEmpty()) {
                continue;
            }
            if (named.vmSite.isEmpty()
                    || !site.startsWith(named.vmSite + "#")) {
                continue;
            }
            if (!sameType(descriptorOfCellType(named.cell), javaType)) {
                continue;
            }
            carriers.add(named.carrier);
        }
        return carriers;
    }

    /** Every write site in the METHOD of one recorded site (not the bci). */
    public List<Site> sitesAt(String recordedSite) {
        List<Site> found = new ArrayList<Site>();
        String site = recordedSite == null ? "" : recordedSite;
        for (Site named : sites) {
            if (WRITE_SITE.equals(named.role) && !named.vmSite.isEmpty()
                    && site.startsWith(named.vmSite + "#")) {
                found.add(named);
            }
        }
        return found;
    }

    /** Regions whose text STORES into each location the slice names, keyed by
     *  both {@code cell} and {@code carrier}. Scoping only: which activations
     *  stored is the recording's. Whole rows are returned because the join
     *  needs the method too (an activation that never entered it wrote
     *  nothing). */
    public Map<String, List<Site>> writeSitesByCell() {
        Map<String, List<Site>> byCell =
                new java.util.LinkedHashMap<String, List<Site>>();
        for (Site site : sites) {
            if (!WRITE_SITE.equals(site.role) || site.regionId.isEmpty()) {
                continue;
            }
            for (String location : new String[]{site.cell, site.carrier}) {
                if (location.isEmpty()) continue;
                List<Site> found = byCell.get(location);
                if (found == null) {
                    found = new ArrayList<Site>();
                    byCell.put(location, found);
                }
                found.add(site);
            }
        }
        return byCell;
    }

    /** Every static write site of one carrier, whatever region runs it. */
    public List<Site> writersOf(String carrier) {
        List<Site> found = new ArrayList<Site>();
        for (Site site : sites) {
            if (WRITE_SITE.equals(site.role)
                    && site.carrier.equals(carrier)) {
                found.add(site);
            }
        }
        return found;
    }

    /** Every static export site feeding one declared port. */
    public List<Site> exportsOf(String portId) {
        List<Site> found = new ArrayList<Site>();
        for (Site site : sites) {
            if (EXPORT_SITE.equals(site.role) && site.portId.equals(portId)) {
                found.add(site);
            }
        }
        return found;
    }

    /** Stores into declared cells the replay must observe (REPORT-P2N). */
    public JsonArray writeSitesOf(Collection<String> declaredCells) {
        JsonArray found = new JsonArray();
        if (declaredCells == null || declaredCells.isEmpty()) return found;
        Set<String> seen = new LinkedHashSet<String>();
        for (Site site : sites) {
            if (!WRITE_SITE.equals(site.role)
                    || !declaredCells.contains(site.cell)
                    || site.declaredCallee.isEmpty()
                    || !seen.add(site.siteId)) {
                continue;
            }
            JsonObject row = new JsonObject();
            row.addProperty("method", methodOfSite(site));
            row.addProperty("unitIndex", SiteId.unitIndexOf(site.siteId));
            row.addProperty("siteId", site.siteId);
            row.addProperty("declaredCallee", site.declaredCallee);
            row.addProperty("cell", site.cell);
            found.add(row);
        }
        return found;
    }

    /** Definition sites of one root cell, within the methods a task
     *  instruments. */
    public JsonArray rootSitesOf(String cell, Set<String> allowedMethods) {
        JsonArray found = new JsonArray();
        String named = cell == null ? "" : cell;
        // One row per site even when several regions hold it.
        Set<String> seen = new LinkedHashSet<String>();
        for (Site site : sites) {
            if (!ROOT_SITE.equals(site.role) || !named.equals(site.cell)) {
                continue;
            }
            String method = methodOfSite(site);
            if (allowedMethods != null && !allowedMethods.contains(method)) {
                continue;
            }
            if (!seen.add(site.siteId + "|" + site.local)) continue;
            JsonObject row = new JsonObject();
            row.addProperty("method", method);
            row.addProperty("local", site.local);
            row.addProperty("unitIndex", SiteId.unitIndexOf(site.siteId));
            row.addProperty("regionId", site.regionId);
            found.add(row);
        }
        return found;
    }

    private static String methodOfSite(Site site) {
        return SiteId.methodOf(site.siteId);
    }

    /** Every DECLARED_SITE, in publication order. Whether any mints is {@link
     *  ConcolicScheduler.SymbolicInputSelection}'s decision. */
    public List<Site> declaredSites() {
        List<Site> found = new ArrayList<Site>();
        for (Site site : sites) {
            if (DECLARED_SITE.equals(site.role) && site.declared != null) {
                found.add(site);
            }
        }
        return found;
    }

    /** The declarations at one site and callee, deduped by candidate edge (a
     *  site several regions hold is still one declaration). Which occurrence
     *  owns the read is the recording's answer. */
    public List<Site> declaredSitesAt(String siteId,
                                      String declaredCallee) {
        List<Site> found = new ArrayList<Site>();
        Set<String> seen = new LinkedHashSet<String>();
        String named = siteId == null ? "" : siteId;
        String callee = declaredCallee == null ? "" : declaredCallee;
        for (Site site : sites) {
            if (!DECLARED_SITE.equals(site.role) || site.declared == null
                    || !named.equals(site.siteId)
                    || !callee.equals(site.declaredCallee)) {
                continue;
            }
            if (!seen.add(site.declared.kind + "|" + site.declared.edgeId
                    + "|" + site.cell + "|"
                    + site.declared.dependencyCell)) {
                continue;
            }
            found.add(site);
        }
        return found;
    }

    /** The annotated target sites this map states. */
    public List<Site> targetSites() {
        List<Site> found = new ArrayList<Site>();
        for (Site site : sites) {
            if (TARGET_SITE.equals(site.role)) found.add(site);
        }
        return found;
    }


    /** A site's method as the VM spells it, {@code
     *  class#name(paramDescriptors)returnDescriptor}: the whole join between a
     *  static site and a recorded endpoint (bci and unit index do not compare).
     */
    static String vmSite(String sootSignature) {
        String value = sootSignature == null ? "" : sootSignature.trim();
        if (!value.startsWith("<") || !value.endsWith(">")) return "";
        int colon = value.indexOf(':');
        int open = value.indexOf('(');
        int close = value.lastIndexOf(')');
        if (colon < 0 || open < colon || close < open) return "";
        String owner = value.substring(1, colon).trim();
        String head = value.substring(colon + 1, open).trim();
        int space = head.lastIndexOf(' ');
        if (space < 0) return "";
        String returnType = head.substring(0, space).trim();
        String name = head.substring(space + 1).trim();
        String parameters = value.substring(open + 1, close).trim();
        StringBuilder descriptor = new StringBuilder();
        descriptor.append(owner).append('#').append(name).append('(');
        if (!parameters.isEmpty()) {
            for (String parameter : parameters.split(",")) {
                descriptor.append(descriptorOf(parameter.trim()));
            }
        }
        return descriptor.append(')').append(descriptorOf(returnType))
                .toString();
    }

    /** Whether a row's type and this map's type can be the same. Disagreement,
     *  not equality: a row may state only the sort ({@code L} = "a reference"),
     *  e.g. every container store; equality would drop those writers. Compare
     *  the sort, and the class only where both name one. */
    private static boolean sameType(String stated, String javaType) {
        String row = rowDescriptor(javaType);
        if (stated.isEmpty() || row.isEmpty()) return true;
        if (stated.charAt(0) != row.charAt(0)) return false;
        // Bare "L": the row named no class.
        if (row.length() == 1 || stated.length() == 1) return true;
        return stated.equals(row);
    }

    /** A row's type as a descriptor; bare sort letters (notably {@code L}) stay
     *  as-is. */
    private static String rowDescriptor(String javaType) {
        String type = javaType == null ? "" : javaType.trim();
        if (type.isEmpty() || type.length() == 1) return type;
        if (type.charAt(0) == '[' || type.endsWith(";")) return type;
        return descriptorOf(type.replace('/', '.'));
    }

    /** The descriptor of the type a declared cell holds, or "". */
    private static String descriptorOfCellType(String cell) {
        FieldPathSpec.DeclaredField declared =
                FieldPathSpec.declaredField(cell);
        return declared == null ? "" : descriptorOf(declared.type());
    }

    /** One Java type name as a JVM descriptor. */
    private static String descriptorOf(String type) {
        String value = type == null ? "" : type.trim();
        StringBuilder array = new StringBuilder();
        while (value.endsWith("[]")) {
            array.append('[');
            value = value.substring(0, value.length() - 2).trim();
        }
        String primitive = primitive(value);
        return array + (primitive.isEmpty()
                ? "L" + value.replace('.', '/') + ";" : primitive);
    }

    private static String primitive(String type) {
        if ("void".equals(type)) return "V";
        if ("boolean".equals(type)) return "Z";
        if ("byte".equals(type)) return "B";
        if ("char".equals(type)) return "C";
        if ("short".equals(type)) return "S";
        if ("int".equals(type)) return "I";
        if ("long".equals(type)) return "J";
        if ("float".equals(type)) return "F";
        if ("double".equals(type)) return "D";
        return "";
    }

    /** The declared field one cell names, or "" when it names none. */
    private static String signature(String cell) {
        FieldPathSpec.DeclaredField declared =
                FieldPathSpec.declaredField(cell);
        return declared == null ? "" : declared.signature();
    }

    private static String string(JsonObject row, String member) {
        JsonElement value = row == null ? null : row.get(member);
        return value == null || value.isJsonNull() ? ""
                : value.getAsString();
    }

    private static String text(Object value) {
        return value == null ? "" : String.valueOf(value).trim();
    }

    private static int integer(Object value) {
        if (value instanceof Number) return ((Number) value).intValue();
        try {
            return Integer.parseInt(text(value));
        } catch (NumberFormatException notANumber) {
            return -1;
        }
    }

    private static List<?> list(Object value) {
        return value instanceof List ? (List<?>) value
                : Collections.emptyList();
    }
}
