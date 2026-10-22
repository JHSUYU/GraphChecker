package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.annotation.Debug;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.contract.ContentPort;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.Validity;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveBoxing;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.strings;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;

public final class StaticScopeMap {
    public static final String FILE = "static_scope_map.jsonl";
    public static final String SITE_KIND = "STATIC_SCOPE_SITE";
    public static final int SCHEMA_VERSION = 1;

    public static final String WRITE_SITE = "WRITE_SITE";
    public static final String EXPORT_SITE = "EXPORT_SITE";
    public static final String TARGET_SITE = "TARGET_SITE";
    public static final String ROOT_SITE = "ROOT_SITE";
    public static final String DECLARED_SITE = "DECLARED_SITE";
    public static final String READ_SITE = "READ_SITE";
    public static final String PROVENANCE_SITE = "PROVENANCE_SITE";

    public static final String ACCESSOR_RETURN = "ACCESSOR_RETURN";
    public static final String CALL_RETURN = "CALL_RETURN";

    public static final String CLOCK_INPUT = "CLOCK";
    public static final String FAULT_INPUT = "FAULT";
    public static final String READ_INPUT = "READ";
    public static final String CONFIG_INPUT = "CONFIG";

    private static final java.util.regex.Pattern LOCAL_CELL =
            java.util.regex.Pattern.compile("^(<.+>)::([^#]+)(?:#.*)?$");

    private static final String PUBLICATION_KIND = "container_publication";
    private static final String[] WRITE_KINDS = {"field_write",
            "field_mutation", "container_mutation_argument",
            "container_call_mutation_effect", "container_array_store_value",
            PUBLICATION_KIND};
    private static final String ACCESSOR_READ = "accessor_field_return";
    private static final Set<String> READ_KINDS = new LinkedHashSet<String>(
            java.util.Arrays.asList("field_read", ACCESSOR_READ));
    private static final String THROW_KIND = "exception_throw";

    public interface Guards {
        List<Guard> of(String siteId);

        default List<Guard> chainOf(String siteId) {
            return Collections.<Guard>emptyList();
        }

        default List<Guard> callsInto(String method,
                                      Predicate<String> walked) {
            return Collections.<Guard>emptyList();
        }

        default List<String> callersOf(String method) {
            return Collections.<String>emptyList();
        }

        default List<Guard> choosingCallsInto(String method) {
            return Collections.<Guard>emptyList();
        }

        default List<Guard> caughtInto(String siteId) {
            return Collections.<Guard>emptyList();
        }

        default Set<String> passable(String siteId,
                                     Predicate<String> entry) {
            return Collections.<String>emptySet();
        }
    }

    public static final class Guard {
        private final String siteId;
        private final Boolean outcome;
        private final Boolean verdict;
        private final List<Guard> deciders;
        private final String via;

        public Guard(String siteId, Boolean outcome) {
            this(siteId, outcome, Collections.<Guard>emptyList());
        }

        public Guard(String siteId, Boolean outcome, List<Guard> deciders) {
            this(siteId, outcome, null, deciders, "");
        }

        public Guard(String siteId, Boolean outcome, Boolean verdict,
                     List<Guard> deciders, String via) {
            this.siteId = siteId == null ? "" : siteId;
            this.outcome = outcome;
            this.verdict = verdict;
            this.deciders = Collections.unmodifiableList(
                    new ArrayList<Guard>(deciders));
            this.via = via == null ? "" : via;
        }

        public List<Guard> deciders() {
            return deciders;
        }

        public String via() {
            return via;
        }

        public Boolean verdict() {
            return verdict;
        }

        public static Set<String> decidingSites(Collection<Guard> guards) {
            Set<String> sites = new LinkedHashSet<String>();
            Deque<Guard> pending = new ArrayDeque<Guard>(guards);
            while (!pending.isEmpty()) {
                Guard guard = pending.pop();
                for (Guard decider : guard.deciders) {
                    sites.add(decider.siteId);
                    pending.push(decider);
                }
            }
            return sites;
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

    public static final class Site {
        public final String role;
        public final String regionId;
        public final String siteId;
        public final String vmSite;
        public final String cell;
        public final String carrier;
        public final String portId;
        public final String declaredCallee;
        public final String local;
        public final Declared declared;
        public final List<String> guards;
        public final List<Boolean> guardOutcomes;
        public final Map<String, List<Guard>> guardDeciders;
        public final List<Guard> chain;
        public final List<String> callers;
        public final String trackedKind;
        public final boolean staticField;
        public final boolean constructionOnly;
        public final String publishedFrom;
        public final int demandDistance;
        public final boolean ownObject;

        Site(String role, String regionId, String siteId, String vmSite,
             String cell, String carrier, String portId,
             String declaredCallee, String local, Declared declared,
             List<String> guards, List<Boolean> guardOutcomes) {
            this(role, regionId, siteId, vmSite, cell, carrier, portId,
                    declaredCallee, local, declared, guards, guardOutcomes,
                    Collections.<String, List<Guard>>emptyMap(),
                    Collections.<Guard>emptyList(),
                    Collections.<String>emptyList(), "", false, false, "",
                    -1, false);
        }

        Site(String role, String regionId, String siteId, String vmSite,
             String cell, String carrier, String portId,
             String declaredCallee, String local, Declared declared,
             List<String> guards, List<Boolean> guardOutcomes,
             Map<String, List<Guard>> guardDeciders, List<Guard> chain,
             List<String> callers, String trackedKind, boolean staticField,
             boolean constructionOnly, String publishedFrom,
             int demandDistance, boolean ownObject) {
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
            this.guardDeciders = Collections.unmodifiableMap(
                    new LinkedHashMap<String, List<Guard>>(guardDeciders));
            this.chain = Collections.unmodifiableList(
                    new ArrayList<Guard>(chain));
            this.callers = Collections.unmodifiableList(
                    new ArrayList<String>(callers));
            this.trackedKind = trackedKind == null ? "" : trackedKind;
            this.staticField = staticField;
            this.constructionOnly = constructionOnly;
            this.publishedFrom = publishedFrom == null ? "" : publishedFrom;
            this.demandDistance = demandDistance;
            this.ownObject = ownObject;
        }

        Site withGuards(List<Guard> found) {
            List<String> sites = new ArrayList<String>();
            List<Boolean> outcomes = new ArrayList<Boolean>();
            Map<String, List<Guard>> deciders =
                    new LinkedHashMap<String, List<Guard>>();
            for (Guard guard : found) {
                sites.add(guard.siteId());
                outcomes.add(guard.outcome());
                if (!guard.deciders().isEmpty()) {
                    deciders.put(guard.siteId(), guard.deciders());
                }
            }
            return copy(regionId, declared, sites, outcomes, deciders, chain,
                    callers);
        }

        Site withChain(List<Guard> found) {
            return copy(regionId, declared, guards, guardOutcomes,
                    guardDeciders, found, callers);
        }

        Site withCallers(List<String> found) {
            return copy(regionId, declared, guards, guardOutcomes,
                    guardDeciders, chain, found);
        }

        Site withDeclared(Declared marked) {
            return copy(regionId, marked, guards, guardOutcomes,
                    guardDeciders, chain, callers);
        }

        Site inRegion(String held) {
            return copy(held, declared, guards, guardOutcomes, guardDeciders,
                    chain, callers);
        }

        private Site copy(String held, Declared stated, List<String> sites,
                          List<Boolean> outcomes,
                          Map<String, List<Guard>> deciders,
                          List<Guard> chained,
                          List<String> calling) {
            return new Site(role, held, siteId, vmSite, cell, carrier,
                    portId, declaredCallee, local, stated, sites, outcomes,
                    deciders, chained, calling, trackedKind, staticField,
                    constructionOnly, publishedFrom, demandDistance,
                    ownObject);
        }

        public Set<String> pathSites() {
            Set<String> sites = new LinkedHashSet<String>(guards);
            for (Guard guard : chain) sites.add(guard.siteId());
            sites.addAll(Guard.decidingSites(chain));
            return sites;
        }

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

    public static final class Declared {
        public final String kind;
        public final String edgeId;
        public final String dependencyCell;
        public final String implementationMethod;
        public final String javaType;
        public final String inputKind;
        public final Clock clock;
        public final ConfigCall config;
        public final String marker;

        public Declared(String kind, String edgeId, String dependencyCell,
                        String implementationMethod, String javaType,
                        String inputKind, Clock clock, ConfigCall config,
                        String marker) {
            this.kind = nonNull(kind);
            this.edgeId = nonNull(edgeId);
            this.dependencyCell = nonNull(dependencyCell);
            this.implementationMethod = nonNull(implementationMethod);
            this.javaType = nonNull(javaType);
            this.inputKind = nonNull(inputKind);
            this.clock = CLOCK_INPUT.equals(this.inputKind) ? clock : null;
            this.config = CONFIG_INPUT.equals(this.inputKind) ? config : null;
            this.marker = FAULT_INPUT.equals(this.inputKind) ? nonNull(marker)
                    : "";
        }
    }

    public static final class ConfigCall {
        public final String sourceId;
        public final String domainMin;
        public final String domainMax;
        public final Validity valid;

        public ConfigCall(String sourceId, String domainMin,
                          String domainMax, Validity valid) {
            this.sourceId = sourceId == null ? "" : sourceId;
            this.domainMin = domainMin == null ? "" : domainMin;
            this.domainMax = domainMax == null ? "" : domainMax;
            this.valid = valid == null ? Validity.ANY : valid;
        }
    }

    public interface ConfigCalls {
        ConfigCall of(String method, int unitIndex, String callee);
    }

    public static final String REGIONS = "region_skeletons.jsonl";

    private final List<Site> sites;
    private final Map<String, Set<String>> regionMethods;

    private final Map<String, List<String>> concreteConfigurationReads;
    private final Map<String, Set<String>> carriers =
            new java.util.concurrent.ConcurrentHashMap<String, Set<String>>();
    private final Map<String, Set<String>> fetches;

    private final Map<String, JsonArray> forcing;

    private StaticScopeMap(List<Site> sites,
                           Map<String, Set<String>> regionMethods,
                           Map<String, List<String>> concreteReads,
                           Map<String, JsonArray> forcing) {
        this(sites, regionMethods, concreteReads, forcing,
                Collections.<String, Set<String>>emptyMap());
    }

    private StaticScopeMap(List<Site> sites,
                           Map<String, Set<String>> regionMethods,
                           Map<String, List<String>> concreteReads,
                           Map<String, JsonArray> forcing,
                           Map<String, Set<String>> fetches) {
        this.sites = Collections.unmodifiableList(sites);
        this.regionMethods = Collections.unmodifiableMap(regionMethods);
        this.concreteConfigurationReads =
                Collections.unmodifiableMap(concreteReads);
        this.forcing = forcing;
        this.fetches = Collections.unmodifiableMap(fetches);
    }

    public StaticScopeMap withPlan(Path regionPlan) {
        Map<String, Set<String>> fetched =
                new LinkedHashMap<String, Set<String>>();
        if (regionPlan != null && Files.isRegularFile(regionPlan)) {
            try {
                for (JsonObject row : ArtifactIO.readJsonl(regionPlan)) {
                    JsonElement stated = row.get(
                            RuntimeSelectedRegionFinalizer.STORE_FETCHES);
                    String occurrence = optionalString(row, "occurrenceId");
                    if (stated == null || !stated.isJsonArray()
                            || occurrence.isEmpty()) {
                        continue;
                    }
                    for (JsonElement fetch : stated.getAsJsonArray()) {
                        fetched.computeIfAbsent(optionalString(
                                fetch.getAsJsonObject(), "location"),
                                key -> new LinkedHashSet<String>())
                                .add(occurrence);
                    }
                }
            } catch (IOException | RuntimeException unreadable) {
                throw new IllegalStateException("REGION_PLAN_UNREADABLE: "
                        + regionPlan, unreadable);
            }
        }
        return new StaticScopeMap(sites, regionMethods,
                concreteConfigurationReads, forcing, fetched);
    }

    public Set<String> storeFetches(String transport, String path) {
        return fetches.getOrDefault(transport + ":" + path,
                Collections.<String>emptySet());
    }

    public Site ownTarget(String targetBranchSite) {
        for (Site target : targetSites()) {
            if (target.guards.contains(targetBranchSite)) return target;
        }
        for (Site target : targetSites()) {
            for (Guard guard : target.chain) {
                if (guard.siteId().equals(targetBranchSite)) return target;
            }
        }
        return null;
    }

    public JsonArray forcing(String targetSiteId) {
        JsonArray table = forcing.get(targetSiteId);
        return table == null ? new JsonArray() : table.deepCopy();
    }

    public Set<String> forcedSites() {
        Set<String> sites = new LinkedHashSet<String>();
        for (JsonArray table : forcing.values()) {
            for (ForcingTable.Arm arm : ForcingTable.read(table).values()) {
                if (!arm.passable) sites.add(arm.siteId);
            }
        }
        return sites;
    }

    public static final String CONFIG_KEY = "CONFIG_KEY";

    public static JsonObject configKeyRow(String sourceId, String mintedAt,
                                          List<String> concreteReads) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", CONFIG_KEY);
        row.addProperty("sourceId", sourceId);
        row.addProperty("mintedAt", mintedAt);
        JsonArray reads = new JsonArray();
        for (String read : concreteReads) reads.add(read);
        row.add("concreteReads", reads);
        return row;
    }

    public List<String> concreteConfigurationReads(String sourceId) {
        List<String> reads = concreteConfigurationReads.get(sourceId);
        return reads == null ? Collections.<String>emptyList() : reads;
    }

    public Set<String> methodsOf(String regionId) {
        Set<String> methods = regionMethods.get(
                regionId == null ? "" : regionId);
        return methods == null ? Collections.<String>emptySet() : methods;
    }


    public static List<Site> sites(
            List<Map<String, Object>> edges,
            List<Map<String, Object>> regions, Map<String, Clock> clocks,
            ConfigCalls configCalls, Demand demand,
            Predicate<String> unwoven,
            Function<String, SharedFieldFlow.TrackedKind> trackedKind,
            Predicate<String> staticField,
            Predicate<String> constructionOnly) {
        Set<String> deciding = decidingCells(edges);
        Map<String, SharedFieldFlow.TrackedKind> kinds =
                new LinkedHashMap<String, SharedFieldFlow.TrackedKind>();
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
                add(found, seen, retained, new Site(TARGET_SITE, "",
                        SiteId.of(method, unitIndex), vmSite(method), "", "",
                        "", "", "", null, NO_GUARDS, NO_OUTCOMES));
                continue;
            }
            addRootSite(found, seen, retained, edge, method, unitIndex);
            addDeclaredSite(found, seen, retained, edge, kind, method,
                    unitIndex, clocks, configCalls, demand, regionRoots);
            if (CALL_RETURN_KIND.equals(kind) && chosen(demand.at(
                    SiteId.of(method, unitIndex), text(edge.get("fromCell"))),
                    SCOPE_DEMAND) && !text(edge.get("invoke")).isEmpty()) {
                addProvenance(found, seen, retained, new Site(PROVENANCE_SITE, "",
                        SiteId.of(method, unitIndex), vmSite(method),
                        text(edge.get("fromCell")), "", "",
                        text(edge.get("invoke")), "", null, NO_GUARDS,
                        NO_OUTCOMES, NO_DECIDERS, NO_CHAIN, NO_CALLERS, "",
                        false, false, "", distance(demand.at(SiteId.of(
                                method, unitIndex), text(edge.get(
                                "fromCell")))), false));
            }
            String field = field(edge);
            if (READ_KINDS.contains(kind)) {
                SharedFieldFlow.TrackedKind tracked =
                        kinds.computeIfAbsent(field, trackedKind);
                String siteId = SiteId.of(method, unitIndex);
                Demanded mark = demand.at(siteId, field);
                if (chosen(mark, PROVENANCE_DEMAND)) {
                    addProvenance(found, seen, retained, new Site(PROVENANCE_SITE, "",
                            siteId, vmSite(method), field, field, "",
                            ACCESSOR_READ.equals(kind)
                                    ? text(edge.get("invoke")) : "", "",
                            null, NO_GUARDS, NO_OUTCOMES, NO_DECIDERS,
                            NO_CHAIN, NO_CALLERS, "", staticField.test(field),
                            false, "", distance(mark), false));
                    continue;
                }
                if ((tracked == SharedFieldFlow.TrackedKind.CONTAINER
                        || constructionOnly.test(field))
                        && chosen(mark, TRACKED_DEMAND)) {
                    addProvenance(found, seen, retained, new Site(
                            PROVENANCE_SITE, "", siteId, vmSite(method),
                            field, field, "", ACCESSOR_READ.equals(kind)
                                    ? text(edge.get("invoke")) : "", "",
                            null, NO_GUARDS, NO_OUTCOMES, NO_DECIDERS,
                            NO_CHAIN, NO_CALLERS, "", staticField.test(field),
                            false, "", distance(mark), false));
                }
                if (tracked != SharedFieldFlow.TrackedKind.NONE
                        && (tracked != SharedFieldFlow.TrackedKind.CONTAINER
                        && deciding.contains(text(edge.get("toCell")))
                        || chosen(mark, TRACKED_DEMAND))) {
                    boolean accessor = ACCESSOR_READ.equals(kind);
                    add(found, seen, retained, new Site(READ_SITE, "",
                            siteId, vmSite(accessor ? text(edge.get(
                                    "accessorImplementationMethod"))
                                    : method), field, field, "",
                            accessor ? text(edge.get("invoke")) : "", "",
                            null, NO_GUARDS, NO_OUTCOMES, NO_DECIDERS,
                            NO_CHAIN, NO_CALLERS, tracked.name(),
                            staticField.test(field), false, "",
                            distance(mark), false));
                }
                continue;
            }
            if (field.isEmpty()) continue;
            String invoke = text(edge.get("invoke"));
            String leaf = SharedFieldFlow.atomicValueField(field, invoke);
            add(found, seen, retained, new Site(WRITE_SITE, "",
                    SiteId.of(method, unitIndex), vmSite(method),
                    leaf.isEmpty() ? field : leaf, field, "", invoke, "",
                    null, NO_GUARDS, NO_OUTCOMES, NO_DECIDERS, NO_CHAIN,
                    NO_CALLERS, "", leaf.isEmpty() && staticField.test(field),
                    invoke.isEmpty() && constructionOnly.test(field),
                    text(edge.get("publishedFrom")), -1,
                    Boolean.TRUE.equals(edge.get("ownObject"))));
        }
        markReads(found, unwoven, demand);
        keepTrackedReads(found, SystemView.current());
        for (Region region : retained) {
            for (Map<String, Object> port : region.ports) {
                if (!"OUT".equals(text(port.get(RuntimeSelectedRegionFinalizer
                        .REGION_PORT_SIDE)))) {
                    continue;
                }
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
                        vmSite(method), text(port.get(
                                CommunicationCatalogContract
                                        .PORT_CODEC_FIELD)), "", portId, "",
                        "", null,
                        Collections.<String>emptyList(),
                        Collections.<Boolean>emptyList()));
            }
        }
        return found;
    }

    private static void markReads(List<Site> found,
                                  Predicate<String> unwoven, Demand demand) {
        Map<String, Set<String>> storers =
                new LinkedHashMap<String, Set<String>>();
        for (Site site : found) {
            if (!WRITE_SITE.equals(site.role)) continue;
            for (String location : new String[]{site.cell, site.carrier}) {
                if (location.isEmpty()) continue;
                storers.computeIfAbsent(location,
                        key -> new LinkedHashSet<String>())
                        .add(site.regionId);
            }
        }
        for (int index = 0; index < found.size(); index++) {
            Site site = found.get(index);
            Declared declared = site.declared;
            if (declared == null || !ACCESSOR_RETURN.equals(declared.kind)
                    || !unwoven.test(declared.implementationMethod)) {
                continue;
            }
            Set<String> regions = storers.getOrDefault(site.cell,
                    Collections.<String>emptySet());
            if (regions.isEmpty() || regions.size() == 1
                    && regions.contains(site.regionId)
                    && !chosen(demand.at(site.siteId, site.cell),
                    Collections.singleton("READ"))) {
                continue;
            }
            found.set(index, site.withDeclared(new Declared(declared.kind,
                    declared.edgeId, declared.dependencyCell,
                    declared.implementationMethod, declared.javaType,
                    READ_INPUT, null, null, "")));
        }
    }

    public static final class Demanded {
        public final String kind;
        public final int distance;
        public final boolean chosen;

        public Demanded(String kind, int distance, boolean chosen) {
            this.kind = kind;
            this.distance = distance;
            this.chosen = chosen;
        }
    }

    public interface Demand {
        Demanded at(String siteId, String cell);
    }

    private static final Set<String> TRACKED_DEMAND = new LinkedHashSet<>(
            Arrays.asList("TRACK", "TRACK_IDENTITY", "TRACK_CONTAINER"));
    private static final Set<String> PROVENANCE_DEMAND =
            Collections.singleton("PROVENANCE");
    private static final Set<String> SCOPE_DEMAND =
            Collections.singleton("SCOPE");
    private static final String CALL_RETURN_KIND = "call_return";

    private static boolean chosen(Demanded mark, Collection<String> kinds) {
        return mark != null && mark.chosen && kinds.contains(mark.kind);
    }

    private static int distance(Demanded mark) {
        return mark == null ? -1 : mark.distance;
    }

    private static final String WIRE_KIND = "wire_handoff";

    private static final int DECIDING_FLOWS = 8;

    private static Set<String> decidingCells(
            List<Map<String, Object>> edges) {
        Map<String, List<String>> into = new LinkedHashMap<String,
                List<String>>();
        List<String> frontier = new ArrayList<String>();
        for (Map<String, Object> edge : edges == null
                ? Collections.<Map<String, Object>>emptyList() : edges) {
            String kind = text(edge.get("kind"));
            String from = text(edge.get("fromCell"));
            if ("guard_dependency".equals(kind)
                    || "exception_guard".equals(kind)) {
                frontier.add(from);
            }
            if (!field(edge).isEmpty() || WIRE_KIND.equals(kind)) continue;
            List<String> sources = into.get(text(edge.get("toCell")));
            if (sources == null) {
                sources = new ArrayList<String>();
                into.put(text(edge.get("toCell")), sources);
            }
            sources.add(from);
        }
        Set<String> deciding = new LinkedHashSet<String>(frontier);
        for (int flow = 0; flow < DECIDING_FLOWS && !frontier.isEmpty();
             flow++) {
            List<String> next = new ArrayList<String>();
            for (String cell : frontier) {
                for (String source : into.getOrDefault(cell,
                        Collections.<String>emptyList())) {
                    if (deciding.add(source)) next.add(source);
                }
            }
            frontier = next;
        }
        return deciding;
    }

    private static void keepTrackedReads(List<Site> found, SystemView view) {
        Set<String> stored = new LinkedHashSet<String>();
        Set<String> beyondView = new LinkedHashSet<String>();
        for (Site site : found) {
            if (!WRITE_SITE.equals(site.role)) continue;
            stored.add(site.cell);
            if (!view.holds(SiteId.methodOf(site.siteId))) {
                beyondView.add(site.cell);
            }
        }
        found.removeIf(site -> READ_SITE.equals(site.role)
                && (!stored.contains(site.cell)
                || SharedFieldFlow.TrackedKind.REFERENCE.name().equals(
                        site.trackedKind)
                && !beyondView.contains(site.cell)));
    }

    public static Set<String> siteIds(Collection<Site> sites) {
        Set<String> ids = new LinkedHashSet<String>();
        for (Site site : sites) ids.add(site.siteId);
        return ids;
    }

    public static List<Guard> targetChain(Guards guards, String siteId,
                                          Predicate<String> entry) {
        List<Guard> chain = new ArrayList<Guard>();
        Set<String> named = new LinkedHashSet<String>();
        for (Guard guard : guards.of(siteId)) named.add(guard.siteId());
        List<Guard> found = new ArrayList<Guard>(guards.chainOf(siteId));
        found.addAll(guards.callsInto(SiteId.methodOf(siteId),
                entry.negate()));
        for (Guard guard : found) {
            if (named.add(guard.siteId())) chain.add(guard);
        }
        return chain;
    }

    public static List<JsonObject> rows(List<Site> sites, Guards guards,
                                        Predicate<String> entry) {
        List<JsonObject> rows = new ArrayList<JsonObject>();
        int writes = 0;
        int caught = 0;
        for (Site site : sites) {
            List<Guard> found = guards == null
                    ? Collections.<Guard>emptyList()
                    : guards.of(site.siteId);
            List<Guard> all = new ArrayList<Guard>(found == null
                    ? Collections.<Guard>emptyList() : found);
            if (WRITE_SITE.equals(site.role) && guards != null) {
                String method = SiteId.methodOf(site.siteId);
                Set<String> named = new LinkedHashSet<String>();
                for (Guard guard : all) named.add(guard.siteId());
                for (Guard guard : site.ownObject
                        ? guards.choosingCallsInto(method)
                        : guards.callsInto(method, callee -> true)) {
                    if (named.add(guard.siteId())) all.add(guard);
                }
                writes++;
                boolean gained = false;
                for (Guard guard : guards.caughtInto(site.siteId)) {
                    if (named.add(guard.siteId())) {
                        all.add(guard);
                        gained = true;
                    }
                }
                if (gained) caught++;
            }
            Site guarded = site.withGuards(all);
            if (WRITE_SITE.equals(site.role) && guards != null) {
                guarded = guarded.withCallers(
                        guards.callersOf(SiteId.methodOf(site.siteId)));
            }
            if (TARGET_SITE.equals(site.role) && guards != null) {
                guarded = guarded.withChain(targetChain(guards, site.siteId,
                        entry));
            }
            JsonObject row = row(guarded);
            if (TARGET_SITE.equals(site.role)) {
                JsonArray force = ForcingTable.of(guarded, guards == null
                        ? Collections.<String>emptySet()
                        : guards.passable(site.siteId, entry));
                if (force.size() > 0) row.add(FORCE, force);
            }
            rows.add(row);
        }
        if (caught > 0) {
            LOG.info("static scope map: {} of {} write site(s) gain the"
                    + " branches deciding a checked throw a handler they are"
                    + " called from catches", caught, writes);
        }
        return rows;
    }

    private static final org.slf4j.Logger LOG =
            org.slf4j.LoggerFactory.getLogger(StaticScopeMap.class);

    static final String FORCE = "force";

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
        if (!site.trackedKind.isEmpty()) {
            row.addProperty("trackedKind", site.trackedKind);
        }
        if (site.staticField) {
            row.addProperty("static", true);
        }
        if (site.constructionOnly) {
            row.addProperty("constructionOnly", true);
        }
        if (site.ownObject) {
            row.addProperty("ownObject", true);
        }
        if (!site.publishedFrom.isEmpty()) {
            row.addProperty("publishedFrom", site.publishedFrom);
        }
        if (site.demandDistance >= 0) {
            row.addProperty("demandDistance", site.demandDistance);
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
            if (!site.declared.inputKind.isEmpty()) {
                row.addProperty("inputKind", site.declared.inputKind);
            }
            if (site.declared.clock != null) {
                row.addProperty("clockNanos", site.declared.clock.nanos());
                if (!site.declared.clock.source().isEmpty()) {
                    row.addProperty("clockSource",
                            site.declared.clock.source());
                }
            }
            if (!site.declared.marker.isEmpty()) {
                row.addProperty("marker", site.declared.marker);
            }
            ConfigCall config = site.declared.config;
            if (config != null) {
                row.addProperty("sourceId", config.sourceId);
                if (!config.domainMin.isEmpty()) {
                    row.addProperty("domainMin", config.domainMin);
                    row.addProperty("domainMax", config.domainMax);
                }
                config.valid.write(row);
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
        if (!site.guardDeciders.isEmpty()) {
            JsonObject deciders = new JsonObject();
            for (Map.Entry<String, List<Guard>> decided
                    : site.guardDeciders.entrySet()) {
                deciders.add(decided.getKey(), guardsJson(decided.getValue()));
            }
            row.add("guardDeciders", deciders);
        }
        if (!site.chain.isEmpty()) {
            JsonArray chain = new JsonArray();
            for (Guard guard : site.chain) chain.add(guardJson(guard));
            row.add("chain", chain);
        }
        if (!site.callers.isEmpty()) {
            JsonArray callers = new JsonArray();
            for (String caller : site.callers) callers.add(caller);
            row.add("callers", callers);
        }
        return row;
    }

    private static JsonObject guardJson(Guard guard) {
        JsonObject json = new JsonObject();
        json.addProperty("siteId", guard.siteId());
        json.addProperty("outcome", guard.outcome());
        if (guard.verdict() != null) {
            json.addProperty("verdict", guard.verdict());
        }
        if (!guard.deciders().isEmpty()) {
            json.add("deciders", guardsJson(guard.deciders()));
        }
        if (!guard.via().isEmpty()) json.addProperty("via", guard.via());
        return json;
    }

    public static JsonArray guardsJson(List<Guard> guards) {
        JsonArray json = new JsonArray();
        for (Guard guard : guards) json.add(guardJson(guard));
        return json;
    }

    public static List<Guard> guardsOf(JsonElement json) {
        List<Guard> guards = new ArrayList<Guard>();
        if (json == null || !json.isJsonArray()) return guards;
        for (JsonElement guard : json.getAsJsonArray()) {
            if (guard.isJsonObject()) guards.add(guardOf(guard.getAsJsonObject()));
        }
        return guards;
    }

    private static Guard guardOf(JsonObject json) {
        return new Guard(optionalString(json, "siteId"),
                flag(json.get("outcome")), flag(json.get("verdict")),
                guardsOf(json.get("deciders")), optionalString(json, "via"));
    }

    private static Boolean flag(JsonElement value) {
        return value == null || value.isJsonNull() ? null
                : Boolean.valueOf(value.getAsBoolean());
    }

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
        for (String regionId : owners(retained, method)) {
            if (!seen.add(ROOT_SITE + "|" + regionId + "|" + siteId + "|"
                    + source + "|" + local.group(2))) {
                continue;
            }
            into.add(new Site(ROOT_SITE, regionId, siteId, vmSite(method),
                    source, "", "", "", local.group(2), null,
                    Collections.<String>emptyList(),
                    Collections.<Boolean>emptyList()));
        }
    }

    private static void addDeclaredSite(
            List<Site> into, Set<String> seen, List<Region> retained,
            Map<String, Object> edge, String kind, String method,
            int unitIndex, Map<String, Clock> clocks,
            ConfigCalls configCalls, Demand demand,
            Set<String> regionMethods) {
        String callee = text(edge.get("invoke"));
        if (callee.isEmpty()) return;
        String cell;
        String implementation = "";
        String inputKind = "";
        Clock clock = null;
        ConfigCall config = "call_return".equals(kind)
                && !regionMethods.contains(callee)
                ? configCalls.of(method, unitIndex, callee) : null;
        if ("accessor_field_return".equals(kind)) {
            cell = firstNonBlank(text(edge.get("declaredFieldSignature")),
                    text(edge.get("fromCell")));
            implementation = text(edge.get("accessorImplementationMethod"));
            if (implementation.isEmpty() || !declaredType(cell, callee, kind)
                    .equals(declaredType(callee, callee, "call_return"))) {
                return;
            }
        } else if ("call_return".equals(kind)
                && clocks.containsKey(callee)
                && !regionMethods.contains(callee)) {
            cell = text(edge.get("fromCell"));
            inputKind = CLOCK_INPUT;
            clock = clocks.get(callee);
        } else if (config != null) {
            cell = text(edge.get("fromCell"));
            inputKind = CONFIG_INPUT;
        } else if ("explicit_symbolic_fault".equals(kind)
                && Debug.isBooleanMarkerSignature(callee)
                && declaredFault(text(edge.get("symbolicName")))) {
            cell = text(edge.get("fromCell"));
            inputKind = FAULT_INPUT;
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
        for (String regionId : owners(retained, method)) {
            if (!seen.add(DECLARED_SITE + "|" + regionId + "|" + siteId
                    + "|" + cell + "|" + callee + "|" + dependencyCell)) {
                continue;
            }
            into.add(new Site(DECLARED_SITE, regionId, siteId,
                    vmSite(method), cell, "", "", callee, "",
                    new Declared(declaredKind, text(edge.get("id")),
                            dependencyCell, implementation, javaType,
                            inputKind, clock, config,
                            text(edge.get("symbolicName"))), NO_GUARDS,
                    NO_OUTCOMES, NO_DECIDERS, NO_CHAIN, NO_CALLERS, "", false,
                    false, "", distance(demand.at(siteId, cell)), false));
        }
    }

    static boolean declaredFault(String name) {
        if (!name.startsWith("FAULT:")) return true;
        String[] parts = name.split(":", -1);
        return parts.length >= 2 && edu.uva.liftlab.graphchecker.causynth
                .LibraryCatalog.transports().contains(parts[1]);
    }

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

    private static final List<String> NO_GUARDS =
            Collections.<String>emptyList();
    private static final List<Boolean> NO_OUTCOMES =
            Collections.<Boolean>emptyList();
    private static final Map<String, List<Guard>> NO_DECIDERS =
            Collections.<String, List<Guard>>emptyMap();
    private static final List<Guard> NO_CHAIN =
            Collections.<Guard>emptyList();
    private static final List<String> NO_CALLERS =
            Collections.<String>emptyList();

    private static void add(List<Site> into, Set<String> seen,
                            List<Region> retained, Site site) {
        for (String regionId : holders(retained,
                SiteId.methodOf(site.siteId))) {
            if (!seen.add(site.role + "|" + regionId + "|" + site.siteId
                    + "|" + site.carrier)) {
                continue;
            }
            into.add(site.inRegion(regionId));
        }
    }

    private static void addProvenance(List<Site> into, Set<String> seen,
                                      List<Region> retained, Site site) {
        if (!holders(retained, SiteId.methodOf(site.siteId)).isEmpty()) {
            add(into, seen, retained, site);
        } else if (seen.add(site.role + "||" + site.siteId + "|"
                + site.carrier)) {
            into.add(site);
        }
    }

    static String field(Map<String, Object> edge) {
        String kind = text(edge.get("kind"));
        if (READ_KINDS.contains(kind)) {
            return signature(firstNonBlank(
                    text(edge.get("declaredFieldSignature")),
                    text(edge.get("fromCell"))));
        }
        return write(kind) ? signature(text(edge.get("toCell"))) : "";
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

    private static List<String> owners(List<Region> retained, String method) {
        List<String> owners = holders(retained, method);
        if (owners.isEmpty()) owners.add("");
        return owners;
    }

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


    public static StaticScopeMap read(Path file) throws IOException {
        if (file == null || !Files.isRegularFile(file)) return empty();
        List<Site> sites = new ArrayList<Site>();
        Map<String, List<String>> concreteReads =
                new LinkedHashMap<String, List<String>>();
        Map<String, JsonArray> forcing =
                new LinkedHashMap<String, JsonArray>();
        for (JsonObject row : ArtifactIO.readJsonl(file)) {
            if (CONFIG_KEY.equals(optionalString(row, "kind"))) {
                concreteReads.put(optionalString(row, "sourceId"),
                        Collections.unmodifiableList(strings(row,
                                "concreteReads")));
                continue;
            }
            if (!SITE_KIND.equals(optionalString(row, "kind"))) continue;
            if (row.has(FORCE) && row.get(FORCE).isJsonArray()) {
                forcing.put(optionalString(row, "siteId"),
                        row.getAsJsonArray(FORCE));
            }
            List<String> guards = strings(row, "guards");
            List<Boolean> outcomes = new ArrayList<Boolean>();
            JsonElement statedOutcomes = row.get("guardOutcomes");
            if (statedOutcomes != null && statedOutcomes.isJsonArray()) {
                for (JsonElement outcome : statedOutcomes.getAsJsonArray()) {
                    outcomes.add(outcome == null || outcome.isJsonNull()
                            ? null : Boolean.valueOf(outcome.getAsBoolean()));
                }
            }
            String declaredKind = optionalString(row, "declaredKind");
            Declared declared = declaredKind.isEmpty() ? null
                    : new Declared(declaredKind, optionalString(row, "edgeId"),
                            optionalString(row, "dependencyCell"),
                            optionalString(row, "implementationMethod"),
                            optionalString(row, "javaType"),
                            optionalString(row, "inputKind"),
                            optionalLongInteger(row, "clockNanos", 0L) > 0L
                                    ? Clock.of(optionalLongInteger(row,
                                            "clockNanos", 0L),
                                            optionalString(row,
                                                    "clockSource"))
                                    : null,
                            new ConfigCall(optionalString(row, "sourceId"),
                                    optionalString(row, "domainMin"),
                                    optionalString(row, "domainMax"),
                                    Validity.read(row)),
                            optionalString(row, "marker"));
            sites.add(new Site(optionalString(row, "role"),
                    optionalString(row, "regionId"),
                    optionalString(row, "siteId"),
                    optionalString(row, "vmSite"),
                    optionalString(row, "cell"),
                    optionalString(row, "carrier"),
                    optionalString(row, "portId"),
                    optionalString(row, "declaredCallee"),
                    optionalString(row, "local"), declared, guards, outcomes,
                    deciders(row), chain(row), strings(row, "callers"),
                    optionalString(row, "trackedKind"),
                    row.has("static") && row.get("static").getAsBoolean(),
                    constructionOnly(row),
                    optionalString(row, "publishedFrom"),
                    (int) optionalLongInteger(row, "demandDistance", -1L),
                    optionalBool(row, "ownObject", false)));
        }
        return new StaticScopeMap(sites, readRegions(file), concreteReads,
                Collections.unmodifiableMap(forcing));
    }

    public static boolean constructionOnly(JsonObject row) {
        JsonElement stated = row.get("constructionOnly");
        return stated != null && stated.isJsonPrimitive()
                && stated.getAsBoolean();
    }

    private static List<Guard> chain(JsonObject row) {
        return guardsOf(row.get("chain"));
    }

    private static Map<String, List<Guard>> deciders(JsonObject row) {
        Map<String, List<Guard>> deciders =
                new LinkedHashMap<String, List<Guard>>();
        JsonElement stated = row.get("guardDeciders");
        if (stated == null || !stated.isJsonObject()) return deciders;
        for (Map.Entry<String, JsonElement> decided
                : stated.getAsJsonObject().entrySet()) {
            deciders.put(decided.getKey(), guardsOf(decided.getValue()));
        }
        return deciders;
    }

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
                    String regionId = optionalString(row, "regionId");
                    if (regionId.isEmpty()) continue;
                    methods.put(regionId, Collections.unmodifiableSet(
                            new LinkedHashSet<String>(strings(row, "methods"))));
                }
            } catch (IOException | RuntimeException unreadable) {
                throw new IllegalStateException(
                        "REGION_SKELETONS_UNREADABLE: " + file, unreadable);
            }
            break;
        }
        return methods;
    }

    public static StaticScopeMap empty() {
        return new StaticScopeMap(new ArrayList<Site>(),
                Collections.<String, Set<String>>emptyMap(),
                Collections.<String, List<String>>emptyMap(),
                Collections.<String, JsonArray>emptyMap());
    }

    public boolean stated() {
        return !sites.isEmpty();
    }

    public Set<String> carriersAt(String recordedSite, String javaType,
                                  LocationKind kind) {
        String site = recordedSite == null ? "" : recordedSite;
        return carriers.computeIfAbsent(site + "|" + javaType + "|" + kind,
                key -> Collections.unmodifiableSet(
                        joinCarriers(site, javaType, kind)));
    }

    private Set<String> joinCarriers(String site, String javaType,
                                     LocationKind kind) {
        Set<String> carriers = new LinkedHashSet<String>();
        for (Site named : ofRole(WRITE_SITE, row -> true)) {
            carriersInMethod(named, site, javaType, kind, carriers);
        }
        for (Site named : ofRole(READ_SITE, row -> true)) {
            carriersInMethod(named, site, javaType, kind, carriers);
        }
        return carriers;
    }



    public boolean demandedAt(String recordedSite, String javaType,
                              LocationKind kind) {
        String site = recordedSite == null ? "" : recordedSite;
        if (kind == LocationKind.STORE && ContentPort.viewed(site)) {
            return true;
        }
        for (Site named : sites) {
            if (PROVENANCE_SITE.equals(named.role)) {
                if (kind == LocationKind.STORE && site.equals(named.siteId)) {
                    return true;
                }
                continue;
            }
            if (named.demandDistance < 0 || named.vmSite.isEmpty()
                    || !site.startsWith(named.vmSite + "#")
                    || !sameType(descriptorOfCellType(named.cell),
                    javaType)) {
                continue;
            }
            if (READ_SITE.equals(named.role) ? stores(named, kind)
                    : named.declared != null
                    && READ_INPUT.equals(named.declared.inputKind)) {
                return true;
            }
        }
        return false;
    }

    private static void carriersInMethod(Site named, String recordedSite,
                                         String javaType, LocationKind kind,
                                         Set<String> carriers) {
        if (!named.vmSite.isEmpty()
                && recordedSite.startsWith(named.vmSite + "#")
                && !named.carrier.isEmpty() && stores(named, kind)
                && sameType(descriptorOfCellType(named.cell), javaType)) {
            carriers.add(named.carrier);
        }
    }

    private static boolean stores(Site site, LocationKind kind) {
        boolean field = kind == (site.staticField ? LocationKind.STATIC
                : LocationKind.INSTANCE);
        if (READ_SITE.equals(site.role)) {
            return field || kind == LocationKind.MAP
                    && JavaContainerTypes.shape(descriptorOfCellType(
                    site.cell)) != JavaContainerTypes.Shape.NONE;
        }
        return site.declaredCallee.isEmpty()
                || SharedFieldFlow.atomicWrite(site.declaredCallee)
                ? field : kind == LocationKind.MAP;
    }

    public List<Site> sitesAt(String recordedSite) {
        String site = recordedSite == null ? "" : recordedSite;
        return ofRole(WRITE_SITE, named -> !named.vmSite.isEmpty()
                && site.startsWith(named.vmSite + "#"));
    }

    public List<Guard> constructionGuards(String recordedSite,
                                          String carrier) {
        Map<String, Guard> guards = new LinkedHashMap<String, Guard>();
        for (Site site : sitesAt(recordedSite)) {
            if (site.publishedFrom.isEmpty()
                    || !site.carrier.equals(carrier)) {
                continue;
            }
            for (int index = 0; index < site.guards.size(); index++) {
                guards.putIfAbsent(site.guards.get(index), new Guard(
                        site.guards.get(index),
                        site.outcomeOf(site.guards.get(index))));
            }
        }
        return new ArrayList<Guard>(guards.values());
    }

    private List<Site> ofRole(String role, Predicate<Site> test) {
        List<Site> found = new ArrayList<Site>();
        for (Site site : sites) {
            if (role.equals(site.role) && test.test(site)) found.add(site);
        }
        return found;
    }

    public Map<String, List<Site>> writeSitesByCell() {
        Map<String, List<Site>> byCell =
                new LinkedHashMap<String, List<Site>>();
        for (Site site : ofRole(WRITE_SITE,
                named -> !named.regionId.isEmpty())) {
            for (String location : new String[]{site.cell, site.carrier}) {
                if (location.isEmpty()) continue;
                byCell.computeIfAbsent(location,
                        key -> new ArrayList<Site>()).add(site);
            }
        }
        return byCell;
    }

    public List<Site> writersOf(String carrier) {
        return ofRole(WRITE_SITE, site -> site.carrier.equals(carrier));
    }

    public List<Site> exportsOf(String portId) {
        if (portId == null) return new ArrayList<Site>();
        Map<String, List<Site>> byPort = exportsByPort;
        if (byPort == null) {
            byPort = new HashMap<String, List<Site>>();
            for (Site site : ofRole(EXPORT_SITE, site -> true)) {
                byPort.computeIfAbsent(site.portId,
                        key -> new ArrayList<Site>()).add(site);
            }
            exportsByPort = byPort;
        }
        return new ArrayList<Site>(byPort.getOrDefault(portId,
                Collections.<Site>emptyList()));
    }

    private volatile Map<String, List<Site>> exportsByPort;

    public JsonArray observedSites() {
        Map<String, Site> tracked = new LinkedHashMap<String, Site>();
        for (Site site : ofRole(READ_SITE, read -> true)) {
            tracked.putIfAbsent(site.cell, site);
        }
        JsonArray found = new JsonArray();
        Map<String, JsonObject> seen = new LinkedHashMap<String, JsonObject>();
        for (Site site : sites) {
            boolean read = READ_SITE.equals(site.role);
            Site cell = tracked.get(site.cell);
            if (!read && !WRITE_SITE.equals(site.role) || cell == null
                    || !site.publishedFrom.isEmpty()) {
                continue;
            }
            boolean call = !site.declaredCallee.isEmpty();
            boolean atomic = SharedFieldFlow.atomicWrite(site.declaredCallee);
            boolean container = holdsContainer(site.cell)
                    && (read || call && !atomic);
            boolean field = read || !call
                    ? !SharedFieldFlow.TrackedKind.CONTAINER.name()
                            .equals(cell.trackedKind)
                    : atomic;
            if (!field && !container || seen.containsKey(site.siteId)) {
                continue;
            }
            JsonObject row = new JsonObject();
            row.addProperty("method", SiteId.methodOf(site.siteId));
            row.addProperty("unitIndex", SiteId.unitIndexOf(site.siteId));
            row.addProperty("siteId", site.siteId);
            row.addProperty("declaredCallee", site.declaredCallee);
            row.addProperty("cell", site.cell);
            row.addProperty("read", read);
            row.addProperty("field", field);
            row.addProperty("container", container);
            row.addProperty("trackedKind", cell.trackedKind);
            if (cell.staticField) row.addProperty("static", true);
            seen.put(site.siteId, row);
            found.add(row);
        }
        for (Site site : ofRole(PROVENANCE_SITE, read -> !read.staticField)) {
            JsonObject held = seen.get(site.siteId);
            if (held != null) {
                held.addProperty("provenance", true);
                continue;
            }
            JsonObject row = new JsonObject();
            row.addProperty("method", SiteId.methodOf(site.siteId));
            row.addProperty("unitIndex", SiteId.unitIndexOf(site.siteId));
            row.addProperty("siteId", site.siteId);
            row.addProperty("declaredCallee", site.declaredCallee);
            row.addProperty("cell", site.cell);
            row.addProperty("read", true);
            row.addProperty("field", false);
            row.addProperty("container", false);
            row.addProperty("provenance", true);
            seen.put(site.siteId, row);
            found.add(row);
        }
        return found;
    }

    private static boolean holdsContainer(String cell) {
        String type = descriptorOfCellType(cell);
        return !type.startsWith("[") && JavaContainerTypes.shape(type)
                != JavaContainerTypes.Shape.NONE;
    }

    public JsonArray rootSitesOf(String cell, Set<String> allowedMethods) {
        JsonArray found = new JsonArray();
        String named = cell == null ? "" : cell;
        Set<String> seen = new LinkedHashSet<String>();
        for (Site site : sites) {
            if (!ROOT_SITE.equals(site.role) || !named.equals(site.cell)) {
                continue;
            }
            String method = SiteId.methodOf(site.siteId);
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

    public Map<String, Clock> clocks() {
        Map<String, Clock> clocks = new LinkedHashMap<String, Clock>();
        for (Site site : ofRole(DECLARED_SITE, site -> site.declared != null
                && CLOCK_INPUT.equals(site.declared.inputKind))) {
            clocks.put(site.declaredCallee, site.declared.clock);
        }
        return clocks;
    }

    public Set<String> readSites() {
        Set<String> reads = new LinkedHashSet<String>();
        for (Site site : ofRole(DECLARED_SITE, site -> site.declared != null
                && READ_INPUT.equals(site.declared.inputKind))) {
            reads.add(readKey(site.siteId, site.cell));
        }
        return reads;
    }

    public List<Site> provenanceSites() {
        return ofRole(PROVENANCE_SITE, read -> true);
    }

    public Map<String, String> provenanceCalls() {
        Map<String, String> calls = new LinkedHashMap<String, String>();
        for (Site site : ofRole(PROVENANCE_SITE,
                read -> !read.declaredCallee.isEmpty())) {
            calls.put(site.siteId, site.cell);
        }
        return calls;
    }

    public Set<String> receiverCells() {
        Set<String> cells = new LinkedHashSet<String>();
        for (Site site : ofRole(PROVENANCE_SITE, read -> true)) {
            cells.add(site.cell);
        }
        for (Site site : declaredSites()) {
            cells.add(site.cell);
        }
        return cells;
    }

    public Set<String> trackedCells() {
        Set<String> cells = new LinkedHashSet<String>();
        for (Site site : ofRole(READ_SITE, read -> true)) {
            cells.add(site.cell);
        }
        return cells;
    }

    public Set<String> trackedRegions() {
        Set<String> regions = new LinkedHashSet<String>();
        for (Site site : ofRole(READ_SITE, read -> true)) {
            regions.add(site.regionId);
        }
        return regions;
    }

    public static String readKey(String siteId, String cell) {
        return siteId + "\n" + cell;
    }

    public List<Site> declaredSites() {
        return ofRole(DECLARED_SITE, site -> site.declared != null);
    }

    public List<Site> declaredSitesAt(String siteId,
                                      String declaredCallee) {
        String named = siteId == null ? "" : siteId;
        String callee = declaredCallee == null ? "" : declaredCallee;
        Set<String> seen = new LinkedHashSet<String>();
        return ofRole(DECLARED_SITE, site -> site.declared != null
                && named.equals(site.siteId)
                && callee.equals(site.declaredCallee)
                && seen.add(site.declared.kind + "|" + site.declared.edgeId
                        + "|" + site.cell + "|"
                        + site.declared.dependencyCell));
    }

    public List<Site> targetSites() {
        return ofRole(TARGET_SITE, site -> true);
    }

    public Boolean fatalArm(String guardSiteId) {
        Boolean found = null;
        for (Site target : targetSites()) {
            Boolean arm = target.outcomeOf(guardSiteId);
            if (arm == null) continue;
            if (found != null && !found.equals(arm)) {
                throw new AmbiguousFatalArm(guardSiteId);
            }
            found = arm;
        }
        return found;
    }

    public static final class AmbiguousFatalArm
            extends IllegalArgumentException {
        public AmbiguousFatalArm(String guardSiteId) {
            super("AMBIGUOUS_FATAL_ARM: " + guardSiteId + " reaches the "
                    + "declared target on both arms");
        }
    }

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

    private static boolean sameType(String stated, String javaType) {
        String row = rowDescriptor(javaType);
        return agree(stated, row)
                || agree(JavaPrimitiveBoxing.valueDescriptor(stated),
                        JavaPrimitiveBoxing.valueDescriptor(row));
    }

    private static boolean agree(String stated, String row) {
        if (stated.isEmpty() || row.isEmpty()) return true;
        if (stated.charAt(0) != row.charAt(0)) return false;
        if (row.length() == 1 || stated.length() == 1) return true;
        return stated.equals(row) || stated.charAt(0) == 'L'
                && mayHold(stated, row);
    }

    private static boolean mayHold(String declared, String runtime) {
        String cell = valueSort(declared);
        String held = valueSort(runtime);
        if (cell.isEmpty() || cell.equals(held)) return true;
        return held.isEmpty() && JavaContainerTypes.shape(declared)
                != JavaContainerTypes.Shape.NONE;
    }

    private static String valueSort(String descriptor) {
        String boxed = JavaPrimitiveBoxing.valueDescriptor(descriptor);
        if (!boxed.equals(descriptor)) return boxed;
        if ("Ljava/lang/String;".equals(descriptor)) return "STRING";
        JavaContainerTypes.Shape shape = JavaContainerTypes.shape(descriptor);
        return shape == JavaContainerTypes.Shape.NONE ? "" : shape.name();
    }

    private static String rowDescriptor(String javaType) {
        String type = javaType == null ? "" : javaType.trim();
        if (type.isEmpty() || type.length() == 1) return type;
        if (type.charAt(0) == '[' || type.endsWith(";")) return type;
        return descriptorOf(type.replace('/', '.'));
    }

    private static String descriptorOfCellType(String cell) {
        FieldPathSpec.DeclaredField declared =
                FieldPathSpec.declaredField(cell);
        return declared == null ? "" : descriptorOf(declared.type());
    }

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

    private static String signature(String cell) {
        FieldPathSpec.DeclaredField declared =
                FieldPathSpec.declaredField(cell);
        return declared == null ? "" : declared.signature();
    }

    static String text(Object value) {
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
