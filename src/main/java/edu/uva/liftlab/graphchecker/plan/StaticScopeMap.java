package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What the static slice knows about the sites the target's demand can reach:
 * one artifact, one row shape (CLOSURE-V2 SS4).
 *
 * <p>The demand is DYNAMIC -- it starts at the values the fatal predicate
 * read in a replay -- so this side publishes only what a program text can
 * state and exploration joins the two:</p>
 *
 * <ul>
 *   <li>{@code WRITE_SITE}: a site that stores into a declared field the
 *       slice named, with the field it stores into ({@code carrier}), the
 *       leaf the VM tracks versions of ({@code cell}), and the region that
 *       would run it.  This generalises {@code declaredInputCells ->
 *       observedWriteSites} (REPORT-P2N) from the cells an experiment
 *       declares to every cell the slice names: the slice is already the
 *       backward cone of the annotated target, so a cell it mentions is
 *       target-relevant by construction and nothing here re-decides
 *       that.</li>
 *   <li>{@code EXPORT_SITE}: a site that defines the value of a declared
 *       wire port, with that {@code portId} -- the producer half of an
 *       interaction whose consumer attaches the port.</li>
 *   <li>{@code TARGET_SITE}: the annotated throw the slice starts at.</li>
 * </ul>
 *
 * <p>Every row carries {@code guards}: the branch sites its own site is
 * control-dependent on, by post-dominance in the enclosing method's CFG
 * (CLOSURE-V2 SS1).  That is the set exploration may flip for the occurrence
 * the row names -- the target's guards for the anchor, a writer's own guards
 * for a writer -- and it is computed where the CFG is
 * ({@link edu.uva.liftlab.graphchecker.causynth} has Soot; this class takes
 * the answer through {@link Guards}).</p>
 *
 * <p>Scoping only.  No row here says what any site wrote, which value any
 * port carried, or which occurrence ran: those are the recording's to
 * state.</p>
 */
public final class StaticScopeMap {
    /** The file this map is published as, beside the other plan artifacts. */
    public static final String FILE = "static_scope_map.jsonl";
    /** Kind of every other row: one site, one shape. */
    public static final String SITE_KIND = "STATIC_SCOPE_SITE";
    public static final int SCHEMA_VERSION = 1;

    public static final String WRITE_SITE = "WRITE_SITE";
    public static final String EXPORT_SITE = "EXPORT_SITE";
    public static final String TARGET_SITE = "TARGET_SITE";

    /** Graph edge kinds that store into a location. */
    private static final String[] WRITE_KINDS = {"field_write",
            "field_mutation", "container_mutation_argument",
            "container_call_mutation_effect", "container_array_store_value"};
    /** The graph edge that names the annotated target. */
    private static final String THROW_KIND = "exception_throw";

    /** The guard set of one site, asked of the stage that has the CFG. */
    public interface Guards {
        /** The branches {@code siteId} is control-dependent on. */
        List<Guard> of(String siteId);
    }

    /**
     * One branch a site is control-dependent on, with the arm that reaches
     * the site.
     *
     * <p>The arm is the site's fatal polarity when the site is the annotated
     * throw: post-dominance keeps a branch exactly when one of its arms makes
     * the site unavoidable and another does not, so that arm is the one a
     * replay must take to reach it.  {@code null} means the branch is not
     * binary (a switch), where no single boolean names an arm.</p>
     */
    public static final class Guard {
        private final String siteId;
        private final Boolean outcome;

        public Guard(String siteId, Boolean outcome) {
            this.siteId = siteId == null ? "" : siteId;
            this.outcome = outcome;
        }

        /** The branch site. */
        public String siteId() {
            return siteId;
        }

        /** The arm of this branch that reaches the guarded site, or null. */
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
        /** The method half of the site as the VM spells an endpoint site. */
        public final String vmSite;
        /** The cell the VM keeps versions of, for a WRITE_SITE. */
        public final String cell;
        /** The declared field that owns {@link #cell}. */
        public final String carrier;
        /** The declared wire port, for an EXPORT_SITE. */
        public final String portId;
        public final List<String> guards;
        /**
         * The arm of each {@link #guards} entry that reaches this site, in
         * the same order; an entry is null when the branch is not binary.
         */
        public final List<Boolean> guardOutcomes;

        Site(String role, String regionId, String siteId, String vmSite,
             String cell, String carrier, String portId,
             List<String> guards, List<Boolean> guardOutcomes) {
            this.role = role;
            this.regionId = regionId;
            this.siteId = siteId;
            this.vmSite = vmSite;
            this.cell = cell;
            this.carrier = carrier;
            this.portId = portId;
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
                    portId, sites, outcomes);
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

    private final List<Site> sites;

    private StaticScopeMap(List<Site> sites) {
        this.sites = Collections.unmodifiableList(sites);
    }

    // ---- building (PLAN) ----------------------------------------------

    /**
     * Every site the slice names, before its guards are computed.
     *
     * @param edges   the candidate graph's rows
     * @param regions the region skeletons: {@code regionId}, {@code methods}
     *                and the declared ports of each
     */
    public static List<Site> sites(List<Map<String, Object>> edges,
                                   List<Map<String, Object>> regions) {
        List<Region> retained = regions(regions);
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
                        "", "", "");
                continue;
            }
            if (!write(kind)) continue;
            String carrier = signature(text(edge.get("toCell")));
            if (carrier.isEmpty()) continue;
            String leaf = SharedFieldFlow.atomicValueField(carrier,
                    text(edge.get("invoke")));
            add(found, seen, retained, WRITE_SITE, method, unitIndex,
                    leaf.isEmpty() ? carrier : leaf, carrier, "");
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
                        vmSite(method), "", "", portId,
                        Collections.<String>emptyList(),
                        Collections.<Boolean>emptyList()));
            }
        }
        return found;
    }

    /** Every site id whose guard set the map states. */
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

    private static void add(List<Site> into, Set<String> seen,
                            List<Region> retained, String role, String method,
                            int unitIndex, String cell, String carrier,
                            String portId) {
        String siteId = SiteId.of(method, unitIndex);
        for (String regionId : holders(retained, method)) {
            if (!seen.add(role + "|" + regionId + "|" + siteId + "|"
                    + carrier)) {
                continue;
            }
            into.add(new Site(role, regionId, siteId, vmSite(method), cell,
                    carrier, portId, Collections.<String>emptyList(),
                    Collections.<Boolean>emptyList()));
        }
    }

    private static boolean write(String kind) {
        for (String write : WRITE_KINDS) {
            if (write.equals(kind)) return true;
        }
        return false;
    }

    /** One region skeleton: what it is called and what it holds. */
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

    /**
     * The region that would run one method: the INNERMOST retained region
     * holding it.
     *
     * <p>Regions nest -- the RPC handler's region holds every method the
     * handler reaches -- and the recording attributes an event to the
     * innermost activation that contains it, so a candidate published under
     * an enclosing region would name every occurrence of the whole request
     * as a writer of one field.  Innermost is minimality under set
     * inclusion, which is a fact about the two method sets and not a
     * ranking; two regions neither of which contains the other are both
     * published, because nothing here may choose between them.</p>
     */
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

    /** The published map, or an empty one when the epoch published none. */
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
            sites.add(new Site(string(row, "role"), string(row, "regionId"),
                    string(row, "siteId"), string(row, "vmSite"),
                    string(row, "cell"), string(row, "carrier"),
                    string(row, "portId"), guards, outcomes));
        }
        return new StaticScopeMap(sites);
    }

    /** No map: every join answers nothing, and says so by being empty. */
    public static StaticScopeMap empty() {
        return new StaticScopeMap(new ArrayList<Site>());
    }

    public boolean stated() {
        return !sites.isEmpty();
    }

    /**
     * The carriers the static slice says one RECORDED write site stores
     * into.
     *
     * <p>The recording names a site the way the VM does -- {@code
     * class#name(descriptor)ret#bci:WRITE} -- and this map names it the way
     * Soot does, so the join is the method the two spellings share plus the
     * type the row was published at: a write row of descriptor {@code I} does
     * not match a site that stores a map.  A row whose type the recording did
     * not state is matched on the method alone.</p>
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
            String stated = descriptorOfCellType(named.cell);
            if (javaType != null && !javaType.isEmpty() && !stated.isEmpty()
                    && !stated.equals(javaType)) {
                continue;
            }
            carriers.add(named.carrier);
        }
        return carriers;
    }

    /**
     * Every write site the map states IN THE METHOD of one recorded site.
     *
     * <p>The join is the method the two spellings share, so this answers
     * about the method and not about the bytecode index inside it.</p>
     */
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

    /** The annotated target sites this map states. */
    public List<Site> targetSites() {
        List<Site> found = new ArrayList<Site>();
        for (Site site : sites) {
            if (TARGET_SITE.equals(site.role)) found.add(site);
        }
        return found;
    }

    // ---- spellings ----------------------------------------------------

    /**
     * The method half of a site as the VM spells one: {@code
     * class#name(paramDescriptors)returnDescriptor}.
     *
     * <p>This is the whole of the join between a static site and a recorded
     * endpoint: the runtime states a bytecode index inside that method and
     * Soot states a unit index, which are two numberings of one method, so
     * the method is what both sides name the same way.</p>
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
