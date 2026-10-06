package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.annotation.Debug;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
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
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.strings;

/**
 * What the static slice knows about the sites the target's demand can reach:
 * one artifact, one row shape (SYMBOL-SCOPE §3). The demand is dynamic, so this
 * side publishes only what program text states; exploration joins the two.
 *
 * <ul>
 *   <li>{@code WRITE_SITE}: a store into a declared field the slice names,
 *       with its {@code carrier} field, versioned leaf {@code cell} and region,
 *       for every cell of the slice.</li>
 *   <li>{@code READ_SITE}: a read of a TRACKED cell the slice both reads
 *       and stores (SYMBOL-SCOPE F2), with its {@code trackedKind}: a
 *       {@code VALUE} -- an instance field holding an integral value, boxed
 *       or not (an atomic's value included) -- or a {@code REFERENCE} a
 *       store re-points, whose referent the reader queries or projects --
 *       whose value a branch decides on, a few flows on and before any
 *       store.  A boxed one is read at the {@code getfield} of its field:
 *       the box's own {@code value}, read through its unboxing accessor, is
 *       a projection of that read, and nothing in the slice stores it.  Its
 *       stores are versioned from the first ({@link #observedSites}), and an
 *       occurrence of a region reading it observes its branches from entry,
 *       so what it decides on shared state joins the writers of that
 *       state.  A read nothing decides on only feeds data -- a token's
 *       bytes, a digest -- where a symbol costs every expression it flows
 *       through and binds nothing.</li>
 *   <li>{@code EXPORT_SITE}: defines the value of a declared wire port
 *       ({@code portId}), the producer half of an interaction.</li>
 *   <li>{@code DECLARED_SITE}: a value entering from outside the slice's
 *       text that a case may declare symbolic -- an {@code ACCESSOR_RETURN} or
 *       a {@code CALL_RETURN} (incl. {@code Debug.makeSymbolicBoolean} fault
 *       markers) -- with the static half of the port it would mint ({@link
 *       Declared}). Scope only: {@code ConcolicScheduler
 *       .SymbolicInputSelection} alone decides admission.</li>
 *   <li>{@code TARGET_SITE}: the declared throw the slice starts at.</li>
 *   <li>{@code ROOT_SITE}: each reached call site defining a {@code
 *       <callee>.return} cell, with the {@code local} it lands in (where
 *       INSTRUMENT binds a {@code LOCAL_DEFINITION}). It names its region by
 *       {@link #holders}, so a mint address is the same in seed and
 *       replay.</li>
 * </ul>
 *
 * <p>Every row carries {@code guards}: the branch sites it is control-dependent
 * on by post-dominance (SYMBOL-SCOPE §3), i.e. what exploration may flip;
 * computed where Soot is, supplied via {@link Guards}.</p>
 *
 * <p>Beside the sites, one {@value #CONFIG_KEY} row per configuration root
 * ({@link #configKeyRow}): the reads of its key no plant stands at.</p>
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
    public static final String READ_SITE = "READ_SITE";

    /** {@code declaredKind}: a field accessor's return; its cell is the field.
     */
    public static final String ACCESSOR_RETURN = "ACCESSOR_RETURN";
    /** {@code declaredKind}: an external call's return; its cell is {@code
     *  <callee>.return}. */
    public static final String CALL_RETURN = "CALL_RETURN";

    /** {@code inputKind}: a clock's reading (causynth.RootCatalog). */
    public static final String CLOCK_INPUT = "CLOCK";
    /** {@code inputKind}: a fault marker's choice. */
    public static final String FAULT_INPUT = "FAULT";
    /** {@code inputKind}: a read of a location another region stores, by an
     *  accessor that runs outside the woven program, so no replay versions
     *  it: a placeholder the closure binds to that location's writers. */
    public static final String READ_INPUT = "READ";
    /** {@code inputKind}: a configuration getter's return
     *  (causynth.ConfigRoots), with its {@code sourceId} and domain. */
    public static final String CONFIG_INPUT = "CONFIG";

    /** A Jimple local cell: {@code <method>::local[#suffix]}. */
    private static final java.util.regex.Pattern LOCAL_CELL =
            java.util.regex.Pattern.compile("^(<.+>)::([^#]+)(?:#.*)?$");

    /** A mutation of the container a local holds, which a later store
     *  publishes into a field ({@code publishedFrom}: that local). */
    private static final String PUBLICATION_KIND = "container_publication";
    private static final String[] WRITE_KINDS = {"field_write",
            "field_mutation", "container_mutation_argument",
            "container_call_mutation_effect", "container_array_store_value",
            PUBLICATION_KIND};
    /** A call that is one read of one field, the read at its call site. */
    private static final String ACCESSOR_READ = "accessor_field_return";
    private static final Set<String> READ_KINDS = new LinkedHashSet<String>(
            java.util.Arrays.asList("field_read", ACCESSOR_READ));
    private static final String THROW_KIND = "exception_throw";

    /** The guard set of one site, asked of the stage that has the CFG. */
    public interface Guards {
        /** The branches {@code siteId} is control-dependent on. */
        List<Guard> of(String siteId);

        /** The guards of those guards, and theirs ({@link Site#chain}); a
         *  guard set with no CFG behind it states none. */
        default List<Guard> chainOf(String siteId) {
            return Collections.<Guard>emptyList();
        }

        /** The guards of the calls that run {@code method}, and theirs, a
         *  few calls up, the calls into a method {@code walked} refuses not
         *  taken: a store runs only where a call into its method did, and
         *  the throw only where its occurrence called its method. */
        default List<Guard> callsInto(String method,
                                      Predicate<String> walked) {
            return Collections.<Guard>emptyList();
        }

        /** The methods of those calls. */
        default List<String> callersOf(String method) {
            return Collections.<String>emptyList();
        }
    }

    /** One branch a site is control-dependent on, with the arm that reaches it
     *  (for the declared throw, the fatal polarity). {@code null} outcome: not
     *  binary (a switch).  A decider (causynth.BooleanReturns) is one too:
     *  one arm of a helper's branch, with its {@link #verdict}. */
    public static final class Guard {
        private final String siteId;
        private final Boolean outcome;
        /** A decider arm's: whether the condition of the guard it decides
         *  holds when this arm runs to the helper's constant return; null
         *  for an OPEN arm, one that runs on to a value no constant states
         *  (and for a guard that is no decider). */
        private final Boolean verdict;
        /** The helper branch arms that decide this guard's arm when the
         *  guard tests the constant a helper returned
         *  (causynth.BooleanReturns), each with its own; none for another
         *  guard. */
        private final List<Guard> deciders;

        public Guard(String siteId, Boolean outcome) {
            this(siteId, outcome, Collections.<Guard>emptyList());
        }

        public Guard(String siteId, Boolean outcome, List<Guard> deciders) {
            this(siteId, outcome, null, deciders);
        }

        public Guard(String siteId, Boolean outcome, Boolean verdict,
                     List<Guard> deciders) {
            this.siteId = siteId == null ? "" : siteId;
            this.outcome = outcome;
            this.verdict = verdict;
            this.deciders = Collections.unmodifiableList(
                    new ArrayList<Guard>(deciders));
        }

        public List<Guard> deciders() {
            return deciders;
        }

        public Boolean verdict() {
            return verdict;
        }

        /** Every decider site under these guards, theirs too. */
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

    /** One site the static slice names, and what it is about. */
    public static final class Site {
        public final String role;
        public final String regionId;
        public final String siteId;
        /** The method half of the site as the VM spells it: the method the
         *  VM records the access in, for a read through an accessor the
         *  accessor's body. */
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
        /** The deciders of those guards that have any, by guard site. */
        public final Map<String, List<Guard>> guardDeciders;
        /**
         * TARGET_SITE: the guards on every path to {@link #guards}, each on
         * its arm toward the throw -- their guards, and theirs, within the
         * method -- and the guards of the calls into the method, up to its
         * execution context's entry ({@link #targetChain}).  An occurrence that decided
         * one of them is an occurrence the failure is about whether or not
         * it went on to the throw: an update that found its routing rule
         * expired never looked the rule's target up, and the expiry is what
         * a witness moves; a block recovery that counted no usable replica
         * never asked for the active NameNode.
         */
        public final List<Guard> chain;
        /** WRITE_SITE: the methods whose calls run the site's method, a few
         *  calls up ({@link Guards#callersOf}): a region running one of them
         *  may run the store though no recorded occurrence entered it. */
        public final List<String> callers;
        /** READ_SITE: how the replay versions its cell, {@code VALUE} or
         *  {@code REFERENCE} ({@link SharedFieldFlow.TrackedKind}); "" on
         *  every other row. */
        public final String trackedKind;
        /** READ_SITE, WRITE_SITE: whether its field is static, whose location
         *  is its class's (an atomic's value never is). */
        public final boolean staticField;
        /** WRITE_SITE: a store into the field itself (no mutator call) that
         *  only its class's construction stores (SYMBOL-SCOPE §5.1): no
         *  guarded store (§5.3, {@code runtime.GuardedStoreSites}). */
        public final boolean constructionOnly;
        /**
         * WRITE_SITE: the local whose container this mutation builds before
         * a later store publishes it into {@link #carrier} (solr-18406's
         * {@code map.put} under {@code !wrapper.isDeleted()} into the map
         * {@code updateKnownCommitPoints} then stores into {@code
         * knownCommits}); "" for a store or mutation of the carrier itself.
         * Its guards shaped the referent the carrier's store publishes
         * ({@link #constructionGuards}).
         */
        public final String publishedFrom;
        /**
         * DECLARED_SITE, READ_SITE: how many edges the root demand found
         * this read from the target's path guards (causynth.RootDemand,
         * SYMBOL-SCOPE §4.6), where it found one; -1 elsewhere.
         */
        public final int demandDistance;

        Site(String role, String regionId, String siteId, String vmSite,
             String cell, String carrier, String portId,
             String declaredCallee, String local, Declared declared,
             List<String> guards, List<Boolean> guardOutcomes) {
            this(role, regionId, siteId, vmSite, cell, carrier, portId,
                    declaredCallee, local, declared, guards, guardOutcomes,
                    Collections.<String, List<Guard>>emptyMap(),
                    Collections.<Guard>emptyList(),
                    Collections.<String>emptyList(), "", false, false, "",
                    -1);
        }

        Site(String role, String regionId, String siteId, String vmSite,
             String cell, String carrier, String portId,
             String declaredCallee, String local, Declared declared,
             List<String> guards, List<Boolean> guardOutcomes,
             Map<String, List<Guard>> guardDeciders, List<Guard> chain,
             List<String> callers, String trackedKind, boolean staticField,
             boolean constructionOnly, String publishedFrom,
             int demandDistance) {
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

        /** This site, declared otherwise. */
        Site withDeclared(Declared marked) {
            return copy(regionId, marked, guards, guardOutcomes,
                    guardDeciders, chain, callers);
        }

        /** This site, held by one region. */
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
                    constructionOnly, publishedFrom, demandDistance);
        }

        /**
         * The decisions an occurrence the failure is about takes on its way to
         * the throw: the deciding guards, and the {@link #chain} with the
         * helper branch that decides a chain guard where one does.  A
         * deciding guard's own decider is the fatal predicate's, the
         * composition's question, and no path decision.
         */
        public Set<String> pathSites() {
            Set<String> sites = new LinkedHashSet<String>(guards);
            for (Guard guard : chain) sites.add(guard.siteId());
            sites.addAll(Guard.decidingSites(chain));
            return sites;
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
        /** {@link #CLOCK_INPUT}, {@link #FAULT_INPUT}, {@link #READ_INPUT},
         *  {@link #CONFIG_INPUT}, or "": a read that stays concrete. */
        public final String inputKind;
        /** A {@link #CLOCK_INPUT}'s clock: the JVM clock it wraps and its
         *  tick (causynth.RootCatalog); null for any other input. */
        public final Clock clock;
        /** A {@link #CONFIG_INPUT}'s root and static domain; null for any
         *  other input. */
        public final ConfigCall config;
        /** A {@link #FAULT_INPUT}'s marker name ({@code
         *  FAULT:<TRANSPORT>:<DIRECTION>[:<Kind>]}, SYMBOL-SCOPE §4.2), so
         *  the replay that answers it knows which door failed; "" for any
         *  other input. */
        public final String marker;

        public Declared(String kind, String edgeId, String dependencyCell,
                        String implementationMethod, String javaType,
                        String inputKind, Clock clock, ConfigCall config,
                        String marker) {
            this.kind = safe(kind);
            this.edgeId = safe(edgeId);
            this.dependencyCell = safe(dependencyCell);
            this.implementationMethod = safe(implementationMethod);
            this.javaType = safe(javaType);
            this.inputKind = safe(inputKind);
            this.clock = CLOCK_INPUT.equals(this.inputKind) ? clock : null;
            this.config = CONFIG_INPUT.equals(this.inputKind) ? config : null;
            this.marker = FAULT_INPUT.equals(this.inputKind) ? safe(marker)
                    : "";
        }

        private static String safe(String value) {
            return value == null ? "" : value;
        }
    }

    /** The configuration root one getter call's return is: {@code
     *  CONFIG:<key>} and the domain its static anchors span ("": none). */
    public static final class ConfigCall {
        public final String sourceId;
        public final String domainMin;
        public final String domainMax;

        public ConfigCall(String sourceId, String domainMin,
                          String domainMax) {
            this.sourceId = sourceId == null ? "" : sourceId;
            this.domainMin = domainMin == null ? "" : domainMin;
            this.domainMax = domainMax == null ? "" : domainMax;
        }
    }

    /** Which call returns are configuration roots, asked of the stage that
     *  recognizes them (causynth.ConfigRoots). */
    public interface ConfigCalls {
        /** The root the return of {@code callee} at {@code
         *  method#uunitIndex} is, or null. */
        ConfigCall of(String method, int unitIndex, String callee);
    }

    /** Region skeletons, published beside {@link #FILE}. */
    public static final String REGIONS = "region_skeletons.jsonl";

    private final List<Site> sites;
    /** Method set of each retained region: the reverse of {@link #holders}.
     *  Needed because under the fold rule a site of region R is recorded under
     *  an enclosing R' ({@code explore.ClosurePlanner#candidates}), which
     *  region-id equality cannot see. Empty when skeletons were absent. */
    private final Map<String, Set<String>> regionMethods;

    /** Each configuration root's reads no plant stands at, by source id. */
    private final Map<String, List<String>> concreteConfigurationReads;

    private StaticScopeMap(List<Site> sites,
                           Map<String, Set<String>> regionMethods,
                           Map<String, List<String>> concreteReads) {
        this.sites = Collections.unmodifiableList(sites);
        this.regionMethods = Collections.unmodifiableMap(regionMethods);
        this.concreteConfigurationReads =
                Collections.unmodifiableMap(concreteReads);
    }

    /** The kind of a configuration root's row. */
    public static final String CONFIG_KEY = "CONFIG_KEY";

    /**
     * One configuration root's row (causynth.ConfigRoots#keyRows): where
     * its plant stands ({@code mintedAt}: its field, or its first getter
     * call), and every other read of its key in the analysed scope ({@code
     * concreteReads}), which a world moving the root leaves at the
     * recording's value.
     */
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

    /** The reads of a configuration root's key no plant stands at; empty
     *  for any other root, or a map that states none. */
    public List<String> concreteConfigurationReads(String sourceId) {
        List<String> reads = concreteConfigurationReads.get(sourceId);
        return reads == null ? Collections.<String>emptyList() : reads;
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
     * @param edges        the candidate graph's rows
     * @param regions      region skeletons: {@code regionId}, {@code methods},
     *                     ports
     * @param clocks       the clocks the slice reads, each with the JVM
     *                     clock it wraps and its tick ({@code
     *                     causynth.RootCatalog}); they bound the {@code
     *                     CALL_RETURN} rows.  {@code
     *                     ACCESSOR_RETURN} rows are bounded by edge kind and
     *                     published whole.
     * @param configCalls  the configuration getter calls the slice reads;
     *                     they are {@code CALL_RETURN} rows too
     * @param demand       the root demand of the slice's reads
     *                     (causynth.RootDemand)
     * @param unwoven      whether a method runs outside the woven program
     * @param trackedKind  how the replay versions a field (SYMBOL-SCOPE F2)
     * @param staticField  whether a field is static
     * @param constructionOnly whether only its class's construction stores
     *                     a field (SYMBOL-SCOPE §5.1)
     */
    public static List<Site> sites(
            List<Map<String, Object>> edges,
            List<Map<String, Object>> regions, Map<String, Clock> clocks,
            ConfigCalls configCalls, Demand demand,
            Predicate<String> unwoven,
            Function<String, SharedFieldFlow.TrackedKind> trackedKind,
            Predicate<String> staticField,
            Predicate<String> constructionOnly) {
        Set<String> deciding = decidingCells(edges);
        // Once per field: a kind can read the field's class's bodies.
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
            String field = field(edge);
            if (READ_KINDS.contains(kind)) {
                SharedFieldFlow.TrackedKind tracked =
                        kinds.computeIfAbsent(field, trackedKind);
                String siteId = SiteId.of(method, unitIndex);
                Demanded mark = demand.at(siteId, field);
                // A read the demand chose decides the anchor's own guard,
                // however many flows away.  A container a final field holds
                // only where the demand chose it: any query of one reaches
                // a branch, so by the deciding rule every final cache a
                // configuration parse reads would be tracked, and its
                // region record from entry (hdfs-adhoc-28's seed:
                // Configuration.CACHE_CLASSES and REGISTRY, WeakHashMaps no
                // model knows, took the DataNode startup region from 13 to
                // 262 recorded decisions).
                if (tracked != SharedFieldFlow.TrackedKind.NONE
                        && (tracked != SharedFieldFlow.TrackedKind.CONTAINER
                        && deciding.contains(text(edge.get("toCell")))
                        || chosen(mark, TRACKED_DEMAND))) {
                    // A read through an accessor call names the accessor:
                    // the replay observes the call's receiver, there being
                    // no getfield of the cell at the site, and the VM
                    // records the read in the accessor's body.
                    boolean accessor = ACCESSOR_READ.equals(kind);
                    add(found, seen, retained, new Site(READ_SITE, "",
                            siteId, vmSite(accessor ? text(edge.get(
                                    "accessorImplementationMethod"))
                                    : method), field, field, "",
                            accessor ? text(edge.get("invoke")) : "", "",
                            null, NO_GUARDS, NO_OUTCOMES, NO_DECIDERS,
                            NO_CHAIN, NO_CALLERS, tracked.name(),
                            staticField.test(field), false, "",
                            distance(mark)));
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
                    text(edge.get("publishedFrom")), -1));
        }
        markReads(found, unwoven, demand);
        keepTrackedReads(found);
        for (Region region : retained) {
            for (Map<String, Object> port : region.ports) {
                // The producer side only: an attach defines no port value,
                // and read as an export it made the consumer's own region a
                // static candidate producer of what it received.
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
                        vmSite(method), "", "", portId, "", "", null,
                        Collections.<String>emptyList(),
                        Collections.<Boolean>emptyList()));
            }
        }
        return found;
    }

    /**
     * Marks {@link #READ_INPUT} each accessor read the weave cannot version
     * (its accessor runs outside the woven program: {@code
     * AtomicInteger.get()}) of a location some other region stores -- or,
     * one the root demand chose, any region (causynth.RootDemand).  A
     * woven read needs no mark: the replay versions it where it runs.
     */
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

    /** What the root demand says of one read (causynth.RootDemand): its
     *  boundary class, its distance from the target's path guards, and
     *  whether it is among the nearest of its class. */
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

    /** The root demand of the slice's reads, by site and cell. */
    public interface Demand {
        /** The boundary a read at {@code siteId} of {@code cell} is, or
         *  null. */
        Demanded at(String siteId, String cell);
    }

    /** The root demand's classes of shared state a replay versions: a
     *  chosen read of one is a {@link #READ_SITE}. */
    private static final Set<String> TRACKED_DEMAND = new LinkedHashSet<>(
            Arrays.asList("TRACK", "TRACK_IDENTITY", "TRACK_CONTAINER"));

    private static boolean chosen(Demanded mark, Collection<String> kinds) {
        return mark != null && mark.chosen && kinds.contains(mark.kind);
    }

    private static int distance(Demanded mark) {
        return mark == null ? -1 : mark.distance;
    }

    private static final String WIRE_KIND = "wire_handoff";

    /** How many flows a read's value may take to a branch operand. */
    private static final int DECIDING_FLOWS = 8;

    /**
     * The cells a branch operand of the slice depends on within {@link
     * #DECIDING_FLOWS} flows, never through a field (a store hands the value
     * to whoever reads the field next, a read of its own) nor across the wire
     * (the receiver decides on its attach, F3): what the occurrence that
     * reads decides on itself.
     */
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

    /** A READ_SITE stays only where the slice stores its cell too: a cell
     *  nothing in the slice writes has no writer to join. */
    private static void keepTrackedReads(List<Site> found) {
        Set<String> stored = new LinkedHashSet<String>();
        for (Site site : found) {
            if (WRITE_SITE.equals(site.role)) stored.add(site.cell);
        }
        found.removeIf(site -> READ_SITE.equals(site.role)
                && !stored.contains(site.cell));
    }

    /** Every site id in {@code sites}. */
    public static Set<String> siteIds(Collection<Site> sites) {
        Set<String> ids = new LinkedHashSet<String>();
        for (Site site : sites) ids.add(site.siteId);
        return ids;
    }

    /**
     * A TARGET_SITE's {@link Site#chain}: the guards of its guards within
     * its method, then those of the calls into its method, a few calls up,
     * never into an execution context's {@code entry} (a thread's or a
     * task's run, a main), which its starter runs: the decisions its
     * occurrence takes on the way to the throw (a block recovery that
     * counted no usable replica never asked for the active NameNode).
     */
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

    /** The artifact's rows: one per site; {@code entry} names the
     *  execution contexts' entries a TARGET_SITE's chain stops at. */
    public static List<JsonObject> rows(List<Site> sites, Guards guards,
                                        Predicate<String> entry) {
        List<JsonObject> rows = new ArrayList<JsonObject>();
        for (Site site : sites) {
            List<Guard> found = guards == null
                    ? Collections.<Guard>emptyList()
                    : guards.of(site.siteId);
            List<Guard> all = new ArrayList<Guard>(found == null
                    ? Collections.<Guard>emptyList() : found);
            if (WRITE_SITE.equals(site.role) && guards != null) {
                // A store is control-dependent on the calls into its
                // method too: a commit point's `deleted` is set by its own
                // delete(), which the deletion policy calls only when the
                // commit's reservation (a clock) has run out.
                Set<String> named = new LinkedHashSet<String>();
                for (Guard guard : all) named.add(guard.siteId());
                for (Guard guard : guards.callsInto(
                        SiteId.methodOf(site.siteId), method -> true)) {
                    if (named.add(guard.siteId())) all.add(guard);
                }
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
            rows.add(row(guarded));
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
        if (!site.trackedKind.isEmpty()) {
            row.addProperty("trackedKind", site.trackedKind);
        }
        if (site.staticField) {
            row.addProperty("static", true);
        }
        if (site.constructionOnly) {
            row.addProperty("constructionOnly", true);
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
        return json;
    }

    /** Guards as rows, each with its deciders: the one spelling the map
     *  and a plan's target branch ({@code decidedBy}) share. */
    public static JsonArray guardsJson(List<Guard> guards) {
        JsonArray json = new JsonArray();
        for (Guard guard : guards) json.add(guardJson(guard));
        return json;
    }

    /** {@link #guardsJson} read back; a member that is no array is none. */
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
                guardsOf(json.get("deciders")));
    }

    private static Boolean flag(JsonElement value) {
        return value == null || value.isJsonNull() ? null
                : Boolean.valueOf(value.getAsBoolean());
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

    /** DECLARED_SITE rows of one candidate edge producing a value from outside
     *  the slice's text: {@code accessor_field_return} (cell = the field);
     *  {@code call_return} of a clock or a configuration getter no region
     *  holds (a region callee already publishes rows; two authorities for
     *  one value is the trap); and {@code explicit_symbolic_fault}, a fault
     *  marker.
     */
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
            // A mint at the accessor's return stands for its field's value:
            // an accessor answering another type (AtomicBoolean.get(), its
            // int value != 0) declares no input.
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
                    false, "", distance(demand.at(siteId, cell))));
        }
    }

    /** Whether a marker is a fault point: a door fault ({@code
     *  FAULT:<TRANSPORT>:<DIRECTION>}) of a library catalog transport; any
     *  other name is the workload's own declaration. */
    static boolean declaredFault(String name) {
        if (!name.startsWith("FAULT:")) return true;
        String[] parts = name.split(":", -1);
        return parts.length >= 2 && edu.uva.liftlab.graphchecker.causynth
                .LibraryCatalog.transports().contains(parts[1]);
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

    /** One row of {@code site} per innermost region holding its method,
     *  once per (role, region, site, carrier). */
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

    /** The field a read or a store of the slice names, or "". */
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

    /** One row per innermost holding region (never choose between
     *  siblings); a method no region holds is published once with region "".
     */
    private static List<String> owners(List<Region> retained, String method) {
        List<String> owners = holders(retained, method);
        if (owners.isEmpty()) owners.add("");
        return owners;
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
        Map<String, List<String>> concreteReads =
                new LinkedHashMap<String, List<String>>();
        for (JsonObject row : ArtifactIO.readJsonl(file)) {
            if (CONFIG_KEY.equals(optionalString(row, "kind"))) {
                concreteReads.put(optionalString(row, "sourceId"),
                        Collections.unmodifiableList(strings(row,
                                "concreteReads")));
                continue;
            }
            if (!SITE_KIND.equals(optionalString(row, "kind"))) continue;
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
                                    optionalString(row, "domainMax")),
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
                    (int) optionalLongInteger(row, "demandDistance", -1L)));
        }
        return new StaticScopeMap(sites, readRegions(file), concreteReads);
    }

    /** A row's {@code constructionOnly}. */
    public static boolean constructionOnly(JsonObject row) {
        JsonElement stated = row.get("constructionOnly");
        return stated != null && stated.isJsonPrimitive()
                && stated.getAsBoolean();
    }

    /** A row's {@code chain}. */
    private static List<Guard> chain(JsonObject row) {
        return guardsOf(row.get("chain"));
    }

    /** A row's {@code guardDeciders}, by guard site. */
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
                    String regionId = optionalString(row, "regionId");
                    if (regionId.isEmpty()) continue;
                    methods.put(regionId, Collections.unmodifiableSet(
                            new LinkedHashSet<String>(strings(row, "methods"))));
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
        return new StaticScopeMap(new ArrayList<Site>(),
                Collections.<String, Set<String>>emptyMap(),
                Collections.<String, List<String>>emptyMap());
    }

    public boolean stated() {
        return !sites.isEmpty();
    }

    /** The carriers the slice says one RECORDED write of one location kind
     *  stores into, joined on the shared method (VM vs Soot spellings), on
     *  the kind of location the site stores ({@link #stores}), and on
     *  whether the carrier's cell may hold the row's type
     *  ({@link #sameType}): the one rule EXPLORE and COMPOSE join a recorded
     *  write to its carrier by.
     */
    public Set<String> carriersAt(String recordedSite, String javaType,
                                  LocationKind kind) {
        Set<String> carriers = new LinkedHashSet<String>();
        String site = recordedSite == null ? "" : recordedSite;
        // A version recorded at a read site is the INITIAL a read's
        // observation started the location's log with: its carrier is the
        // field read.
        for (Site named : ofRole(WRITE_SITE, row -> true)) {
            carriersInMethod(named, site, javaType, kind, carriers);
        }
        for (Site named : ofRole(READ_SITE, row -> true)) {
            carriersInMethod(named, site, javaType, kind, carriers);
        }
        return carriers;
    }

    /**
     * Whether one RECORDED read is a read the root demand found on the
     * declared throw's path guards (causynth.RootDemand: a {@link
     * #READ_SITE} or a READ placeholder stating its {@code demandDistance}),
     * joined as {@link #carriersAt} joins: on the shared method, the kind of
     * location and the type.
     */
    public boolean demandedAt(String recordedSite, String javaType,
                              LocationKind kind) {
        String site = recordedSite == null ? "" : recordedSite;
        for (Site named : sites) {
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

    /**
     * Whether a site stores (or, read, starts the log of) a location of this
     * kind: a field store, or an atomic's write of its value leaf, a field --
     * static or instance as its field is;
     * any other mutator call the state of the container its carrier holds;
     * a read the field it reads and, of a container field, that
     * container's state.  No site of the map names an array element, so an
     * element's write joins no carrier (hdfs-17899-bug1 r4: an element
     * stored in {@code PBHelper.convert} took a reference field's).
     */
    private static boolean stores(Site site, LocationKind kind) {
        // A static field's location is its class's, an instance field's its
        // object's: one never stands for the other.
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

    /** Every write site in the METHOD of one recorded site (not the bci). */
    public List<Site> sitesAt(String recordedSite) {
        String site = recordedSite == null ? "" : recordedSite;
        return ofRole(WRITE_SITE, named -> !named.vmSite.isEmpty()
                && site.startsWith(named.vmSite + "#"));
    }

    /**
     * The construction guards of a reference store (R3-REFCONT SS1.6, D5):
     * the guards, each on the arm that reaches it, of every mutation the
     * METHOD of one recorded store of {@code carrier} makes on a container
     * it then publishes into that carrier ({@link Site#publishedFrom}).  A
     * decision that skipped a mutation leaves no node in the referent's
     * state, so the referent a writer published rests on these decisions of
     * its occurrence as much as on the mutations it did make.  Per method,
     * like {@link #sitesAt}: bci and unit index do not compare.
     */
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

    /** The sites of one role {@code test} holds for, in publication order. */
    private List<Site> ofRole(String role, Predicate<Site> test) {
        List<Site> found = new ArrayList<Site>();
        for (Site site : sites) {
            if (role.equals(site.role) && test.test(site)) found.add(site);
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

    /** Every static write site of one carrier, whatever region runs it. */
    public List<Site> writersOf(String carrier) {
        return ofRole(WRITE_SITE, site -> site.carrier.equals(carrier));
    }

    /** Every static export site feeding one declared port. */
    public List<Site> exportsOf(String portId) {
        return ofRole(EXPORT_SITE, site -> site.portId.equals(portId));
    }

    /**
     * Every access of a tracked cell ({@link #READ_SITE}), each observed
     * when it runs: a store, so the replay versions the cell from it and a
     * read of the cell has a writer to join whatever value the store wrote
     * (for every cell); and a read, so a location no store of the window
     * reached still has a log -- its INITIAL -- that the read states and the
     * closure asks the cell's writers about (GreyGraph §3.1's Writers_W(l),
     * SYMBOL-SCOPE §5.5).  A row says what it observes: {@code field}, the
     * cell on its holder before the access (a {@code CONTAINER} cell's
     * reference never changes, so its constructor's store is none); and
     * {@code container}, the state of the container a cell holds -- the
     * read's referent after a read, the call's receiver before a container
     * mutation -- so its in-place mutations are versions and a query reads
     * one (SYMBOL-SCOPE §5.2).  A mutator call is never a field
     * observation, except an atomic's write of its value: its receiver is
     * not the cell's holder.  Each row states its cell's {@code
     * trackedKind}, and a static cell's {@code static}: its location is its
     * declaring class's, observed on the class's mirror.  Not observed here:
     * a mutation of a container a local holds before its publication
     * ({@link Site#publishedFrom}), whose receiver is that local's
     * container, not the carrier's -- its log starts at its first model
     * event.
     */
    public JsonArray observedSites() {
        Map<String, Site> tracked = new LinkedHashMap<String, Site>();
        for (Site site : ofRole(READ_SITE, read -> true)) {
            tracked.putIfAbsent(site.cell, site);
        }
        JsonArray found = new JsonArray();
        Set<String> seen = new LinkedHashSet<String>();
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
            if (!field && !container || !seen.add(site.siteId)) continue;
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
            found.add(row);
        }
        return found;
    }

    /** Whether a cell holds a map, set, list, queue or deque (an array's
     *  elements are locations of their own). */
    private static boolean holdsContainer(String cell) {
        String type = descriptorOfCellType(cell);
        return !type.startsWith("[") && JavaContainerTypes.shape(type)
                != JavaContainerTypes.Shape.NONE;
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

    /** The clocks the slice reads: every {@link #CLOCK_INPUT} site's
     *  callee, with the JVM clock it wraps and its tick. */
    public Map<String, Clock> clocks() {
        Map<String, Clock> clocks = new LinkedHashMap<String, Clock>();
        for (Site site : ofRole(DECLARED_SITE, site -> site.declared != null
                && CLOCK_INPUT.equals(site.declared.inputKind))) {
            clocks.put(site.declaredCallee, site.declared.clock);
        }
        return clocks;
    }

    /** The reads into a placeholder, one per {@link #READ_INPUT} site, as
     *  {@link #readKey}: the SITE, never the cell alone, since a cell names
     *  a field of every object of its type ({@code AtomicInteger.value}). */
    public Set<String> readSites() {
        Set<String> reads = new LinkedHashSet<String>();
        for (Site site : ofRole(DECLARED_SITE, site -> site.declared != null
                && READ_INPUT.equals(site.declared.inputKind))) {
            reads.add(readKey(site.siteId, site.cell));
        }
        return reads;
    }

    /** The cells a replay versions its reads of ({@link #READ_SITE}): a
     *  read of one can be paired with another writer. */
    public Set<String> trackedCells() {
        Set<String> cells = new LinkedHashSet<String>();
        for (Site site : ofRole(READ_SITE, read -> true)) {
            cells.add(site.cell);
        }
        return cells;
    }

    /** The regions reading a tracked cell ({@link #READ_SITE}). */
    public Set<String> trackedRegions() {
        Set<String> regions = new LinkedHashSet<String>();
        for (Site site : ofRole(READ_SITE, read -> true)) {
            regions.add(site.regionId);
        }
        return regions;
    }

    /** One read's key: its site and the location it reads. */
    public static String readKey(String siteId, String cell) {
        return siteId + "\n" + cell;
    }

    /** Every DECLARED_SITE, in publication order. Whether any mints is {@link
     *  ConcolicScheduler.SymbolicInputSelection}'s decision. */
    public List<Site> declaredSites() {
        return ofRole(DECLARED_SITE, site -> site.declared != null);
    }

    /** The declarations at one site and callee, deduped by candidate edge (a
     *  site several regions hold is still one declaration). Which occurrence
     *  owns the read is the recording's answer. */
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

    /** The declared target sites this map states. */
    public List<Site> targetSites() {
        return ofRole(TARGET_SITE, site -> true);
    }

    /** The arm of one branch site that reaches the declared target, from the
     *  TARGET_SITE guards ({@code causynth.SiteControlDependence}). {@code
     *  null}: no arm stated, which the caller refuses (never a default).
     *
     *  @throws AmbiguousFatalArm where the guard reaches a declared target on
     *          both arms: no one arm is the fatal one */
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

    /** A guard that reaches a declared target on both arms ({@link
     *  #fatalArm}): a refusal a caller names, never a crash. */
    public static final class AmbiguousFatalArm
            extends IllegalArgumentException {
        public AmbiguousFatalArm(String guardSiteId) {
            super("AMBIGUOUS_FATAL_ARM: " + guardSiteId + " reaches the "
                    + "declared target on both arms");
        }
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

    /** Whether a row's type and this map's type can be the same, as stated or
     *  as the values they hold: a wrapper location holds its primitive's
     *  value ({@link JavaPrimitiveBoxing#valueDescriptor}) or null, so it
     *  agrees with a row of that primitive (a stored box states its value,
     *  {@code J} for a {@code Long}) and with a reference row (a stored null
     *  states {@code L}).  solr-18413: {@code RoutingRule.expireAt}'s writes
     *  said {@code J} and joined no carrier. */
    private static boolean sameType(String stated, String javaType) {
        String row = rowDescriptor(javaType);
        return agree(stated, row)
                || agree(JavaPrimitiveBoxing.valueDescriptor(stated),
                        JavaPrimitiveBoxing.valueDescriptor(row));
    }

    /** Disagreement, not equality: a row may state only the sort ({@code L}
     *  = "a reference"), e.g. every container store; equality would drop
     *  those writers. Compare the sort, and, where both name a class, whether
     *  the cell may hold the row's ({@link #mayHold}). */
    private static boolean agree(String stated, String row) {
        if (stated.isEmpty() || row.isEmpty()) return true;
        if (stated.charAt(0) != row.charAt(0)) return false;
        // Bare "L": the row named no class.
        if (row.length() == 1 || stated.length() == 1) return true;
        return stated.equals(row) || stated.charAt(0) == 'L'
                && mayHold(stated, row);
    }

    /**
     * Whether a location of one declared class may hold an object of
     * another: a store states its object's runtime class, the cell its
     * declared type, and no class hierarchy is at hand here.  So by the value
     * sorts COMPOSE types either by ({@code compose.JavaSmtSorts}): a
     * container's shape ({@link JavaContainerTypes#shape}, by interface), a
     * String, a box's value.  A declared class none of them names (an
     * application class, an interface, {@code Object}) may be a supertype
     * of any; a runtime class none names may implement a container's
     * interface, but is no String and no box, which are final.  SOLR-18406:
     * the {@code Map} field {@code knownCommits} holding a
     * {@code ConcurrentHashMap}.
     */
    private static boolean mayHold(String declared, String runtime) {
        String cell = valueSort(declared);
        String held = valueSort(runtime);
        if (cell.isEmpty() || cell.equals(held)) return true;
        return held.isEmpty() && JavaContainerTypes.shape(declared)
                != JavaContainerTypes.Shape.NONE;
    }

    /** A reference descriptor's value sort, or "" when it names none. */
    private static String valueSort(String descriptor) {
        String boxed = JavaPrimitiveBoxing.valueDescriptor(descriptor);
        if (!boxed.equals(descriptor)) return boxed;
        if ("Ljava/lang/String;".equals(descriptor)) return "STRING";
        JavaContainerTypes.Shape shape = JavaContainerTypes.shape(descriptor);
        return shape == JavaContainerTypes.Shape.NONE ? "" : shape.name();
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
