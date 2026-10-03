package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import soot.Body;
import soot.FastHierarchy;
import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.CmpExpr;
import soot.jimple.CmpgExpr;
import soot.jimple.CmplExpr;
import soot.jimple.ConditionExpr;
import soot.jimple.Constant;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.LongConstant;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.StringConstant;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.MHGPostDominatorsFinder;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.text;

/**
 * Configuration values a program reads, recognized by category from the
 * program text rather than declared per case (SYMBOL-SCOPE §4.3), as {@link
 * RootCatalog} recognizes clocks:
 * <ul>
 *   <li>a GETTER: a JVM one ({@code System.getProperty}, {@code
 *       System.getenv}, {@code Boolean.getBoolean}, {@code
 *       Integer.getInteger}, {@code Long.getLong}) or a {@code CONFIG_SOURCE}
 *       row of the library catalog ({@link LibraryCatalog}: Hadoop's {@code
 *       Configuration.get*}, Solr's cluster properties and {@code
 *       XmlConfigFile}), called on its class or a subclass;</li>
 *   <li>a WRAPPER: a method each of whose returns is a configuration value
 *       ({@link #valueOf}) of one key in one shape -- a literal key, or the
 *       wrapper's own String parameter -- followed {@value #MAX_DEPTH} deep:
 *       Solr's {@code "true".equals(getClusterProperty(LEGACY_CLOUD,
 *       "false"))}.  A getter call in a wrapper's body is the wrapper's
 *       read: its callers mint it;</li>
 *   <li>a FIELD: an integral or boolean instance field each writer of which
 *       ({@link StaticProgram#fieldWriters}, the whole analysed scope)
 *       stores a configuration value of one key in one shape, as hdfs-17960's
 *       {@code SnapshotManager.snapshotDeletionOrdered} = {@code
 *       conf.getBoolean(DFS_NAMENODE_SNAPSHOT_DELETION_ORDERED, false)} in
 *       its constructor -- a constant store excepted where a store of the
 *       configuration post-dominates it (an initializer it overwrites) --; or
 *       a field of a {@code CONFIG_FIELD_OWNER} class, which is its own
 *       key.  A getter call its writers store is the field's read.</li>
 * </ul>
 * A configuration value is a getter's or wrapper's return through locals,
 * casts, a parse or an unboxing ({@code parseInt}, {@code booleanValue},
 * {@code trim}, ...), a literal's {@code equals} (a VIEW) and {@code
 * Math.max}/{@code min} with a constant (a CLAMP); arithmetic makes another
 * value.
 *
 * <p>Its key is the key argument where it is a literal (javac inlines a
 * {@code static final String}); a key no literal names is no root.  A source
 * is {@code CONFIG:<key>}, or {@code CONFIG:<key>==<literal>} for a view:
 * {@code "a".equals(get(k))} is not {@code k}.  One key is one root, minted
 * in one shape (its view, clamps and type): the key's first field (by
 * signature) where a field holds it, else every call reading it in the
 * shape of its first call (by site).  The VM names a field mint by its
 * owner's class and a symbol by its source, so every other read of the key
 * is read concretely (SYMBOL-SCOPE §7).</p>
 *
 * <p>An integral source's domain is the hull of its anchors: each getter's
 * literal default and {@code c - 1, c, c + 1} for each integral literal
 * {@code c} a branch compares its value with within {@value #FLOWS} flows
 * of the slice, never through a field; then through its clamps, whose
 * image a planted value must lie in.  The mint adds the value it read
 * ({@code runtime.ActiveRegion}).</p>
 *
 * <p>What is not minted is named ({@link #gaps}, {@code DECLARATION_MISSING}
 * DIAGNOSTIC): a read of a key no literal names ({@value #KEY_UNRESOLVED}),
 * a field a constant store can leave holding the constant ({@value
 * #FIELD_OVERWRITTEN}), and a read of a minted key in another shape
 * ({@value #READ_CONCRETE}).</p>
 */
final class ConfigRoots {
    /** The prefix of every configuration source id. */
    static final String PREFIX = "CONFIG:";
    /** Between a key and the literal its view compares it with. */
    static final String VIEW = "==";
    /** A read whose key no literal names: read concretely. */
    static final String KEY_UNRESOLVED = "CONFIG_KEY_UNRESOLVED";
    /** A field a constant store can leave holding the constant. */
    static final String FIELD_OVERWRITTEN = "CONFIG_FIELD_OVERWRITTEN";
    /** A read of a key minted in another shape: read concretely. */
    static final String READ_CONCRETE = "CONFIG_READ_CONCRETE";
    /** How many wrappers deep a getter is followed. */
    private static final int MAX_DEPTH = 4;
    /** How many flows a compared literal may stand from the value. */
    private static final int FLOWS = 8;

    /** The JVM's own configuration getters: signature, key, default. */
    private static final Object[][] JVM_GETTERS = {
        {"<java.lang.System: java.lang.String getProperty(java.lang.String)>",
                0, -1},
        {"<java.lang.System: java.lang.String getProperty(java.lang.String,"
                + "java.lang.String)>", 0, 1},
        {"<java.lang.System: java.lang.String getenv(java.lang.String)>",
                0, -1},
        {"<java.lang.Boolean: boolean getBoolean(java.lang.String)>", 0, -1},
        {"<java.lang.Integer: java.lang.Integer getInteger("
                + "java.lang.String)>", 0, -1},
        {"<java.lang.Integer: java.lang.Integer getInteger("
                + "java.lang.String,int)>", 0, 1},
        {"<java.lang.Integer: java.lang.Integer getInteger("
                + "java.lang.String,java.lang.Integer)>", 0, 1},
        {"<java.lang.Long: java.lang.Long getLong(java.lang.String)>", 0, -1},
        {"<java.lang.Long: java.lang.Long getLong(java.lang.String,long)>",
                0, 1},
        {"<java.lang.Long: java.lang.Long getLong(java.lang.String,"
                + "java.lang.Long)>", 0, 1},
    };

    /** A configuration value's parse or unboxing: the same key, read under
     *  another type. */
    private static final Set<String> PARSES = new LinkedHashSet<>(
            Arrays.asList(
                    "<java.lang.Boolean: boolean parseBoolean(java.lang.String)>",
                    "<java.lang.Boolean: java.lang.Boolean valueOf(java.lang.String)>",
                    "<java.lang.Integer: int parseInt(java.lang.String)>",
                    "<java.lang.Integer: java.lang.Integer valueOf(java.lang.String)>",
                    "<java.lang.Long: long parseLong(java.lang.String)>",
                    "<java.lang.Long: java.lang.Long valueOf(java.lang.String)>",
                    "<java.lang.Boolean: boolean booleanValue()>",
                    "<java.lang.Integer: int intValue()>",
                    "<java.lang.Long: long longValue()>",
                    "<java.lang.String: java.lang.String trim()>"));
    private static final String EQUALS =
            "<java.lang.String: boolean equals(java.lang.Object)>";
    /** A clamp: whether it is a floor ({@code max}) or a ceiling. */
    private static final Map<String, Boolean> CLAMPS = new HashMap<>();
    static {
        CLAMPS.put("<java.lang.Math: int max(int,int)>", Boolean.TRUE);
        CLAMPS.put("<java.lang.Math: long max(long,long)>", Boolean.TRUE);
        CLAMPS.put("<java.lang.Math: int min(int,int)>", Boolean.FALSE);
        CLAMPS.put("<java.lang.Math: long min(long,long)>", Boolean.FALSE);
    }
    private static final Set<String> MINTABLE = new LinkedHashSet<>(
            Arrays.asList("boolean", "byte", "char", "short", "int",
                    "long"));
    private static final Set<String> READS = new LinkedHashSet<>(
            Arrays.asList("field_read", "accessor_field_return"));
    private static final Set<String> GUARDS = new LinkedHashSet<>(
            Arrays.asList("guard_dependency", "exception_guard"));

    /** One configuration root: its id, its Java type, its static domain. */
    static final class Source {
        final String sourceId;
        final String javaType;
        /** The hull of the anchors, or "" (a boolean, or none found). */
        final String domainMin;
        final String domainMax;

        private Source(String sourceId, String javaType, String domainMin,
                       String domainMax) {
            this.sourceId = sourceId;
            this.javaType = javaType;
            this.domainMin = domainMin;
            this.domainMax = domainMax;
        }
    }

    /** {@code Math.max(v, bound)} (a floor) or {@code Math.min(v, bound)}. */
    private static final class Clamp {
        final boolean floor;
        final BigInteger bound;

        Clamp(boolean floor, BigInteger bound) {
            this.floor = floor;
            this.bound = bound;
        }

        BigInteger apply(BigInteger value) {
            return floor ? value.max(bound) : value.min(bound);
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Clamp && floor == ((Clamp) other).floor
                    && bound.equals(((Clamp) other).bound);
        }

        @Override
        public int hashCode() {
            return Objects.hash(floor, bound);
        }
    }

    /**
     * A configuration value at one point of a body: its key -- or the
     * parameter that states it, or neither (no literal names it) -- the view
     * and clamps it is read through, innermost first, and the defaults its
     * getters name.
     */
    private static final class ConfigValue {
        final String key;
        final int keyParam;
        final String view;
        final List<Clamp> clamps;
        final List<BigInteger> defaults;

        ConfigValue(String key, int keyParam, String view, List<Clamp> clamps,
                    List<BigInteger> defaults) {
            this.key = key;
            this.keyParam = keyParam;
            this.view = view;
            this.clamps = clamps;
            this.defaults = defaults;
        }

        /** The same value: one key in one shape (its defaults may differ). */
        boolean sameShape(ConfigValue other) {
            return other != null && keyParam == other.keyParam
                    && Objects.equals(key, other.key)
                    && Objects.equals(view, other.view)
                    && clamps.equals(other.clamps);
        }

        /** {@code "literal".equals(this)}: a view of a raw value only. */
        ConfigValue viewed(String literal) {
            if (view != null || !clamps.isEmpty()) return null;
            return new ConfigValue(key, keyParam, literal, clamps, defaults);
        }

        /** {@code Math.max}/{@code min} of this: an integral value only. */
        ConfigValue clamped(Clamp clamp) {
            if (view != null) return null;
            List<Clamp> through = new ArrayList<>(clamps);
            through.add(clamp);
            return new ConfigValue(key, keyParam, view, through, defaults);
        }

        ConfigValue withDefaults(List<BigInteger> more) {
            List<BigInteger> all = new ArrayList<>(defaults);
            all.addAll(more);
            return new ConfigValue(key, keyParam, view, clamps, all);
        }

        /** Its root's id: the key, and the literal of its view. */
        String sourceId() {
            return PREFIX + key + (view == null ? "" : VIEW + view);
        }
    }

    /** A getter: which argument is its key, which its default; or a
     *  wrapper of one, its key fixed or one of its parameters, with the
     *  view and clamps its returns read the key through. */
    private static final class Getter {
        final int keyArg;
        final int defaultArg;
        /** A wrapper's own key, or null when an argument states it. */
        final String key;
        final String view;
        final List<Clamp> clamps;
        final List<BigInteger> defaults;

        Getter(int keyArg, int defaultArg) {
            this(keyArg, defaultArg, null, null,
                    Collections.<Clamp>emptyList(),
                    Collections.<BigInteger>emptyList());
        }

        Getter(int keyArg, int defaultArg, String key, String view,
               List<Clamp> clamps, List<BigInteger> defaults) {
            this.keyArg = keyArg;
            this.defaultArg = defaultArg;
            this.key = key;
            this.view = view;
            this.clamps = clamps;
            this.defaults = defaults;
        }
    }

    /** What a field's writers store: its value, or why no read of it is a
     *  root. */
    private static final class FieldValue {
        final ConfigValue value;
        final Refusal refusal;

        FieldValue(ConfigValue value, Refusal refusal) {
            this.value = value;
            this.refusal = refusal;
        }
    }

    /** One getter call the slice reads a return of. */
    private static final class Read {
        final Map<String, Object> edge;
        final String method;
        final int unitIndex;
        final String callee;
        final String type;
        final ConfigValue value;

        Read(Map<String, Object> edge, String method, int unitIndex,
             String callee, String type, ConfigValue value) {
            this.edge = edge;
            this.method = method;
            this.unitIndex = unitIndex;
            this.callee = callee;
            this.type = type;
            this.value = value;
        }

        String site() {
            return SiteId.render(method, unitIndex);
        }
    }

    /** The one shape a key is minted in: its field's, or its first
     *  call's. */
    private static final class Shape {
        final String sourceId;
        final String javaType;
        final ConfigValue value;
        /** Where it is minted: the field, or the first call's site. */
        final String at;
        final boolean field;

        Shape(String sourceId, String javaType, ConfigValue value, String at,
              boolean field) {
            this.sourceId = sourceId;
            this.javaType = javaType;
            this.value = value;
            this.at = at;
            this.field = field;
        }

        /** Whether a call's return is this shape's: one symbol for both. */
        boolean takes(Read read) {
            return !field && javaType.equals(read.type)
                    && value.sameShape(read.value);
        }
    }

    /** A configuration read no root mints, named ({@link #gaps}). */
    private static final class Refusal {
        final String reason;
        final String method;
        final String siteId;
        /** The source the key is minted as elsewhere, or "". */
        final String sourceId;
        final String detail;

        Refusal(String reason, String method, String siteId, String sourceId,
                String detail) {
            this.reason = reason;
            this.method = method;
            this.siteId = siteId;
            this.sourceId = sourceId;
            this.detail = detail;
        }
    }

    private final Map<String, Getter> getters = new HashMap<>();
    /** The methods whose answer is being computed (a cycle reads them). */
    private final Set<String> open = new HashSet<>();
    /** The declared field of each key, and its source. */
    private final Map<String, Source> fields = new TreeMap<>();
    /** The declared call sites ({@code method#uN|callee}) and their
     *  sources. */
    private final Map<String, Source> calls = new TreeMap<>();
    /** Every configuration field of the slice, declared or not. */
    private final Set<String> configFields = new TreeSet<>();
    /** Every getter or wrapper callee of the slice's call returns. */
    private final Set<String> configCallees = new TreeSet<>();
    /** The configuration reads no root mints. */
    private final List<Refusal> refusals = new ArrayList<>();
    /** The getter calls a configuration field's writers store: the field's
     *  reads, minted (or refused) there. */
    private final Set<String> fieldReads = new HashSet<>();
    /** The same, per field. */
    private final Map<String, Set<String>> fieldStoredReads = new HashMap<>();
    /** Each key's one shape, by key. */
    private final Map<String, Shape> shapes = new HashMap<>();
    /** What each field of the scope holds, once asked ({@link #census}). */
    private final Map<String, FieldValue> fieldValues = new HashMap<>();
    /** Each application field's store sites, over the analysed scope. */
    private Map<String, List<String>> fieldWriters =
            Collections.emptyMap();

    private ConfigRoots() {
    }

    /**
     * The configuration roots of one slice.
     *
     * @param edges        the candidate graph
     * @param fieldWriters each application field's store sites ({@code
     *                     <method>#u<unit>}), over the whole analysed scope
     */
    static ConfigRoots of(Collection<Map<String, Object>> edges,
                          Map<String, List<String>> fieldWriters) {
        ConfigRoots roots = new ConfigRoots();
        roots.fieldWriters = fieldWriters;
        Map<String, List<Map<String, Object>>> out = new HashMap<>();
        Map<String, List<Map<String, Object>>> guardsFrom = new HashMap<>();
        Set<String> readFields = new TreeSet<>();
        Map<String, List<Map<String, Object>>> callSites = new TreeMap<>();
        for (Map<String, Object> edge : edges) {
            String kind = text(edge.get("kind"));
            String from = text(edge.get("fromCell"));
            (GUARDS.contains(kind) ? guardsFrom : out).computeIfAbsent(from,
                    ignored -> new ArrayList<>()).add(edge);
            if (READS.contains(kind)) {
                String field = MapFields.firstNonEmpty(
                        text(edge.get("declaredFieldSignature")), from);
                if (!field.isEmpty()) readFields.add(field);
            }
            if ("call_return".equals(kind)
                    && !text(edge.get("invoke")).isEmpty()) {
                callSites.computeIfAbsent(text(edge.get("invoke")),
                        ignored -> new ArrayList<>()).add(edge);
            }
        }
        // One key, one shape: its first field, by signature, else its first
        // call, by site.
        Map<String, Shape> shapes = roots.shapes;
        for (String field : readFields) {
            FieldValue stored = roots.fieldValue(field, fieldWriters);
            if (stored == null) continue;
            roots.configFields.add(field);
            if (stored.refusal != null) {
                roots.refusals.add(stored.refusal);
                continue;
            }
            ConfigValue value = stored.value;
            Shape held = shapes.get(value.key);
            if (held != null) {
                roots.refusals.add(concrete("", field, field, held));
                continue;
            }
            Source source = roots.source(value.sourceId(), fieldType(field),
                    value.defaults, value.clamps,
                    Collections.singleton(field), out, guardsFrom);
            shapes.put(value.key, new Shape(source.sourceId, source.javaType,
                    value, field, true));
            roots.fields.put(field, source);
        }
        List<Read> reads = roots.reads(callSites);
        for (Read read : reads) {
            if (read.value.key != null && MINTABLE.contains(read.type)
                    && !shapes.containsKey(read.value.key)) {
                shapes.put(read.value.key, new Shape(read.value.sourceId(),
                        read.type, read.value, read.site(), false));
            }
        }
        Map<Shape, List<Read>> minted = new LinkedHashMap<>();
        for (Read read : reads) {
            if (read.value.key == null) {
                if (MINTABLE.contains(read.type)) {
                    roots.refusals.add(new Refusal(KEY_UNRESOLVED,
                            read.method, read.site(), "", read.callee
                            + " reads a key no literal names, so its return"
                            + " is read concretely: a configuration root is"
                            + " one key's"));
                }
                continue;
            }
            Shape shape = shapes.get(read.value.key);
            // A key no read of which is mintable (a String): no root.
            if (shape == null) continue;
            if (shape.takes(read)) {
                minted.computeIfAbsent(shape, ignored -> new ArrayList<>())
                        .add(read);
            } else {
                roots.refusals.add(concrete(read.method, read.site(),
                        read.callee + " (" + read.type + ")", shape));
            }
        }
        for (Map.Entry<Shape, List<Read>> shape : minted.entrySet()) {
            Set<String> cells = new LinkedHashSet<>();
            List<BigInteger> defaults = new ArrayList<>();
            for (Read read : shape.getValue()) {
                cells.add(text(read.edge.get("toCell")));
                defaults.addAll(read.value.defaults);
            }
            Shape key = shape.getKey();
            Source source = roots.source(key.sourceId, key.javaType,
                    defaults, key.value.clamps, cells, out, guardsFrom);
            for (Read read : shape.getValue()) {
                roots.calls.put(callSite(read.method, read.unitIndex,
                        read.callee), source);
            }
        }
        return roots;
    }

    /** The getter calls whose returns the slice reads, by site; a call in
     *  a wrapper's body is the wrapper's, one a configuration field's writer
     *  stores the field's. */
    private List<Read> reads(
            Map<String, List<Map<String, Object>>> callSites) {
        List<Read> reads = new ArrayList<>();
        for (Map.Entry<String, List<Map<String, Object>>> callee
                : callSites.entrySet()) {
            SootMethodRef reference = reference(callee.getKey());
            if (reference == null) continue;
            Getter getter = getter(reference, 0);
            if (getter == null) continue;
            configCallees.add(callee.getKey());
            String type = reference.getReturnType().toString();
            for (Map<String, Object> edge : callee.getValue()) {
                String method = text(edge.get("method"));
                int unitIndex = MapFields.number(edge.get("unitIndex"), -1);
                SootMethodRef caller = reference(method);
                if (caller != null && getter(caller, 0) != null
                        || fieldReads.contains(SiteId.render(method,
                        unitIndex))) {
                    continue;
                }
                Body body = CausynthStaticFacts.activeBody(
                        CausynthStaticFacts.method(method));
                InvokeExpr invoke = invokeOf(unitAt(body, unitIndex));
                if (invoke == null) continue;
                reads.add(new Read(edge, method, unitIndex, callee.getKey(),
                        type, called(getter, invoke, body)));
            }
        }
        reads.sort(Comparator.<Read, String>comparing(read -> read.method)
                .thenComparingInt(read -> read.unitIndex)
                .thenComparing(read -> read.callee));
        return reads;
    }

    /** A read of a key minted in another shape, read concretely. */
    private static Refusal concrete(String method, String siteId,
                                    String what, Shape shape) {
        return new Refusal(READ_CONCRETE, method, siteId, shape.sourceId,
                what + " reads the configuration concretely: its key is"
                        + " minted once, as " + shape.sourceId + " ("
                        + shape.javaType + ") at " + shape.at + ", and this"
                        + " read takes it in another shape (another field,"
                        + " view, clamp or type, or a getter beside the"
                        + " key's field)");
    }

    /** The same recognition, minting only these roots ({@link
     *  RootDemand#configSources}); a read left concrete beside a root
     *  not chosen is no gap. */
    ConfigRoots limitedTo(Set<String> sourceIds) {
        ConfigRoots limited = new ConfigRoots();
        limited.configFields.addAll(configFields);
        limited.configCallees.addAll(configCallees);
        for (Map.Entry<String, Source> field : fields.entrySet()) {
            if (sourceIds.contains(field.getValue().sourceId)) {
                limited.fields.put(field.getKey(), field.getValue());
            }
        }
        for (Map.Entry<String, Source> call : calls.entrySet()) {
            if (sourceIds.contains(call.getValue().sourceId)) {
                limited.calls.put(call.getKey(), call.getValue());
            }
        }
        for (Refusal refusal : refusals) {
            if (refusal.sourceId.isEmpty()
                    || sourceIds.contains(refusal.sourceId)) {
                limited.refusals.add(refusal);
            }
        }
        return limited;
    }

    /** The root a read of {@code field} mints, or null when it mints none:
     *  no configuration field, or not its key's declared one. */
    Source field(String field) {
        return fields.get(field);
    }

    /** Every declared configuration field and its root. */
    Map<String, Source> fields() {
        return Collections.unmodifiableMap(fields);
    }

    /** The root the return of {@code callee} at {@code method#uunitIndex}
     *  mints, or null when it mints none. */
    Source call(String method, int unitIndex, String callee) {
        return calls.get(callSite(method, unitIndex, callee));
    }

    /** Whether a field of the slice holds a configuration, declared or
     *  not. */
    boolean configField(String field) {
        return configFields.contains(field);
    }

    /** The slice's callees that are configuration getters or wrappers of
     *  one: roots, never a scope frontier. */
    Set<String> callees() {
        return Collections.unmodifiableSet(configCallees);
    }

    /**
     * One {@code CONFIG_KEY} row per chosen root ({@code
     * StaticScopeMap#configKeyRow}): where its plant stands, and every
     * other read of its key in the analysed scope ({@link #census}), which a
     * world moving the key leaves at the recording's value -- no
     * configuration a cluster could hold while one is left ({@code
     * compose.ClaimPolicy}).
     *
     * @param plantedFieldReads the configuration field reads the regions
     *                          declare ({@link StaticSymbolicSourceDiscovery}),
     *                          each woven to plant the world's value
     */
    List<JsonObject> keyRows(Set<String> sourceIds,
                             Set<String> plantedFieldReads) {
        Map<String, Set<String>> reads = census();
        Map<String, Shape> chosen = new TreeMap<>();
        for (Shape shape : shapes.values()) {
            if (sourceIds.contains(shape.sourceId)) {
                chosen.put(shape.sourceId, shape);
            }
        }
        List<JsonObject> rows = new ArrayList<>();
        for (Shape shape : chosen.values()) {
            // Where a plant stands: the field's declared reads, else the
            // minted getter calls.  The getter calls the field's writers
            // store are the field's own, overwritten at every planted read.
            Set<String> planted = new HashSet<>();
            Set<String> stored = shape.field ? fieldStoredReads.getOrDefault(
                    shape.at, Collections.<String>emptySet())
                    : Collections.<String>emptySet();
            if (shape.field) planted.addAll(plantedFieldReads);
            for (Map.Entry<String, Source> call : calls.entrySet()) {
                if (call.getValue().sourceId.equals(shape.sourceId)) {
                    planted.add(call.getKey().substring(0,
                            call.getKey().indexOf('|')));
                }
            }
            List<String> concrete = new ArrayList<>();
            boolean minted = false;
            for (String site : reads.getOrDefault(shape.value.key,
                    Collections.<String>emptySet())) {
                if (planted.contains(site)) {
                    minted = true;
                } else if (!stored.contains(site)) {
                    concrete.add(site);
                }
            }
            // A key no read of which is planted (a field a tree's hook owns,
            // or read outside every region) is no engine root.
            if (minted) {
                rows.add(StaticScopeMap.configKeyRow(shape.sourceId,
                        shape.at, concrete));
            }
        }
        return rows;
    }

    /**
     * Every read of a configuration key in the analysed scope (its
     * application classes), by key: each call of a JVM or catalog getter or
     * of a wrapper the recognition found, in any shape -- a known wrapper's
     * own body is its callers' read --, and each read of a field holding
     * the key.  A wrapper outside the slice is not followed: its getter call
     * is the read.
     */
    private Map<String, Set<String>> census() {
        Map<String, Set<String>> reads = new HashMap<>();
        List<SootClass> classes = new ArrayList<>(
                Scene.v().getApplicationClasses());
        classes.sort(Comparator.comparing(SootClass::getName));
        for (SootClass type : classes) {
            List<SootMethod> methods = new ArrayList<>(type.getMethods());
            methods.sort(Comparator.comparing(SootMethod::getSignature));
            for (SootMethod method : methods) {
                if (!method.isConcrete()
                        || getters.get(method.getSignature()) != null) {
                    continue;
                }
                Body body = CausynthStaticFacts.activeBody(method);
                if (body == null) continue;
                int index = 0;
                for (Unit unit : body.getUnits()) {
                    String key = keyRead(unit, body);
                    if (key != null) {
                        reads.computeIfAbsent(key,
                                ignored -> new TreeSet<>()).add(
                                SiteId.render(method.getSignature(), index));
                    }
                    index++;
                }
            }
        }
        return reads;
    }

    /** The key one unit reads, or null: a known getter's call, or a read
     *  of a field holding one key. */
    private String keyRead(Unit unit, Body body) {
        InvokeExpr invoke = invokeOf(unit);
        if (invoke != null) {
            Getter getter = libraryGetter(invoke.getMethodRef());
            if (getter == null) {
                getter = getters.get(invoke.getMethodRef().getSignature());
            }
            return getter == null ? null : called(getter, invoke, body).key;
        }
        if (!(unit instanceof AssignStmt) || !(((AssignStmt) unit)
                .getRightOp() instanceof FieldRef)) {
            return null;
        }
        String field = CausynthStaticFacts.declaredFieldSignature(
                ((FieldRef) ((AssignStmt) unit).getRightOp()).getFieldRef());
        if (!fieldValues.containsKey(field)) {
            fieldValues.put(field, fieldValue(field, fieldWriters));
        }
        FieldValue held = fieldValues.get(field);
        return held == null || held.value == null ? null : held.value.key;
    }

    /**
     * The configuration reads no root mints, one catalog gap row each
     * ({@code communication_gaps.jsonl.gz}): {@code DECLARATION_MISSING},
     * DIAGNOSTIC, the reason first in its detail.
     */
    List<Map<String, Object>> gaps() {
        List<Map<String, Object>> rows = new ArrayList<>();
        for (Refusal refusal : refusals) {
            rows.add(CommunicationCatalogPlanner.gap(
                    GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    refusal.reason, refusal.method, refusal.siteId,
                    refusal.reason + ": " + refusal.detail));
        }
        return rows;
    }

    private static String callSite(String method, int unitIndex,
                                   String callee) {
        return SiteId.render(method, unitIndex) + "|" + callee;
    }

    /** A root read at {@code cells}, its domain from its defaults and the
     *  literals the slice compares those cells with, through its clamps. */
    private Source source(String sourceId, String javaType,
                          List<BigInteger> defaults, List<Clamp> clamps,
                          Collection<String> cells,
                          Map<String, List<Map<String, Object>>> out,
                          Map<String, List<Map<String, Object>>> guardsFrom) {
        if ("boolean".equals(javaType)) {
            return new Source(sourceId, javaType, "", "");
        }
        List<BigInteger> spread = new ArrayList<>(defaults);
        for (BigInteger compared : comparedLiterals(cells, out, guardsFrom)) {
            spread.add(compared.subtract(BigInteger.ONE));
            spread.add(compared);
            spread.add(compared.add(BigInteger.ONE));
        }
        if (spread.isEmpty()) {
            return new Source(sourceId, javaType, "", "");
        }
        // No floor at 0: `if (limit < 0)` compares with 0, and -1 is the
        // value that flips it.
        BigInteger min = Collections.min(spread);
        BigInteger max = Collections.max(spread);
        // A clamp's value lies in its image: Math.max(v, 1) is never 0, so
        // no plant may write 0 where it stores.  Monotone: the hull's ends.
        for (Clamp clamp : clamps) {
            min = clamp.apply(min);
            max = clamp.apply(max);
        }
        return new Source(sourceId, javaType, min.toString(), max.toString());
    }

    /**
     * The integral literals a branch compares a value with, the value read
     * at {@code cells} and carried at most {@value #FLOWS} flows forward,
     * never into or out of a field.
     */
    private static List<BigInteger> comparedLiterals(
            Collection<String> cells,
            Map<String, List<Map<String, Object>>> out,
            Map<String, List<Map<String, Object>>> guardsFrom) {
        Set<String> seen = new LinkedHashSet<>(cells);
        List<String> frontier = new ArrayList<>(cells);
        Set<BigInteger> literals = new TreeSet<>();
        Set<String> branches = new HashSet<>();
        for (int flow = 0; flow <= FLOWS && !frontier.isEmpty(); flow++) {
            List<String> next = new ArrayList<>();
            for (String cell : frontier) {
                for (Map<String, Object> guard : guardsFrom.getOrDefault(cell,
                        Collections.<Map<String, Object>>emptyList())) {
                    String method = text(guard.get("method"));
                    int unitIndex = MapFields.number(guard.get("unitIndex"),
                            -1);
                    if (branches.add(SiteId.render(method, unitIndex))) {
                        literals.addAll(comparedAt(method, unitIndex));
                    }
                }
                for (Map<String, Object> edge : out.getOrDefault(cell,
                        Collections.<Map<String, Object>>emptyList())) {
                    String to = text(edge.get("toCell"));
                    // A store hands the value to the field's next reader.
                    if (fieldCell(to) || !seen.add(to)) continue;
                    next.add(to);
                }
            }
            frontier = next;
        }
        return new ArrayList<>(literals);
    }

    /** The integral literals the branch at {@code method#uunitIndex}
     *  compares with, directly or through a {@code long} {@code cmp}. */
    private static List<BigInteger> comparedAt(String method, int unitIndex) {
        Body body = CausynthStaticFacts.activeBody(
                CausynthStaticFacts.method(method));
        Unit unit = unitAt(body, unitIndex);
        if (!(unit instanceof IfStmt) || !(((IfStmt) unit).getCondition()
                instanceof ConditionExpr)) {
            return Collections.emptyList();
        }
        ConditionExpr condition = (ConditionExpr) ((IfStmt) unit)
                .getCondition();
        Value[] sides = {condition.getOp1(), condition.getOp2()};
        for (Value operand : sides) {
            Value compared = operand instanceof Local
                    ? uniqueDefinition(body, (Local) operand) : null;
            // `cmp a, b` against 0: the literal is cmp's.
            if (compared instanceof CmpExpr || compared instanceof CmplExpr
                    || compared instanceof CmpgExpr) {
                sides = new Value[]{
                        ((soot.jimple.BinopExpr) compared).getOp1(),
                        ((soot.jimple.BinopExpr) compared).getOp2()};
                break;
            }
        }
        List<BigInteger> found = new ArrayList<>();
        for (Value side : sides) {
            if (literal(side) != null) found.add(literal(side));
        }
        return found;
    }

    /**
     * What {@code field} holds, or null when it is no configuration: not an
     * integral or boolean instance field, or a writer storing anything but a
     * constant or a configuration value of one key in one shape.  A field of
     * a configuration class is its own key.  Not minted, named: a value of a
     * key no literal names, and a constant store no store of the
     * configuration post-dominates (the field may hold it, as {@code if (f
     * <= 0) f = 1} after {@code f = get(k)}).
     */
    private FieldValue fieldValue(String field,
                                  Map<String, List<String>> fieldWriters) {
        SootField declared = Scene.v().grabField(field);
        if (declared == null || declared.isStatic()
                || !MINTABLE.contains(declared.getType().toString())) {
            return null;
        }
        if (LibraryCatalog.configFieldOwners().contains(
                declared.getDeclaringClass().getName())) {
            return new FieldValue(new ConfigValue(field, -1, null,
                    Collections.<Clamp>emptyList(),
                    Collections.<BigInteger>emptyList()), null);
        }
        Map<String, Body> bodies = new HashMap<>();
        Set<String> through = new HashSet<>();
        Map<String, List<Unit>> constants = new LinkedHashMap<>();
        Map<String, List<Unit>> stores = new HashMap<>();
        ConfigValue stored = null;
        String unresolved = null;
        for (String writer : fieldWriters.getOrDefault(field,
                Collections.<String>emptyList())) {
            String method = SiteId.methodOf(writer);
            Body body = CausynthStaticFacts.activeBody(
                    CausynthStaticFacts.method(method));
            Unit unit = unitAt(body, SiteId.unitIndexOf(writer));
            if (!(unit instanceof AssignStmt)
                    || !(((AssignStmt) unit).getLeftOp() instanceof FieldRef)) {
                return null;
            }
            bodies.put(method, body);
            Value right = ((AssignStmt) unit).getRightOp();
            if (right instanceof Constant) {
                constants.computeIfAbsent(method,
                        ignored -> new ArrayList<>()).add(unit);
                continue;
            }
            ConfigValue value = valueOf(right, body, 0, through);
            if (value == null) return null;
            if (value.key == null) {
                if (unresolved == null) unresolved = writer;
                continue;
            }
            if (stored != null && !stored.sameShape(value)) return null;
            stored = stored == null ? value : stored.withDefaults(
                    value.defaults);
            stores.computeIfAbsent(method, ignored -> new ArrayList<>())
                    .add(unit);
        }
        if (unresolved != null || stored != null) {
            // The getter calls it stores are its reads, not the slice's.
            fieldReads.addAll(through);
            fieldStoredReads.put(field, through);
        }
        if (unresolved != null) {
            return new FieldValue(null, new Refusal(KEY_UNRESOLVED,
                    SiteId.methodOf(unresolved), unresolved, "", field
                    + " stores a configuration of a key no literal names,"
                    + " so its reads stay concrete"));
        }
        if (stored == null) return null;
        for (Map.Entry<String, List<Unit>> method : constants.entrySet()) {
            Body body = bodies.get(method.getKey());
            for (Unit constant : method.getValue()) {
                if (overwritten(body, constant, stores.get(method.getKey()))) {
                    continue;
                }
                String site = SiteId.render(method.getKey(),
                        indexOf(body, constant));
                return new FieldValue(null, new Refusal(FIELD_OVERWRITTEN,
                        method.getKey(), site, "", field + " may hold the"
                        + " constant stored at " + site + ": no store of "
                        + stored.sourceId() + " follows it on every path,"
                        + " so its reads stay concrete"));
            }
        }
        return new FieldValue(stored, null);
    }

    /** Whether a store of the configuration post-dominates {@code store}
     *  in its method: an initializer every path overwrites. */
    private static boolean overwritten(Body body, Unit store,
                                       List<Unit> configured) {
        if (configured == null) return false;
        MHGPostDominatorsFinder<Unit> post =
                new MHGPostDominatorsFinder<>(new BriefUnitGraph(body));
        for (Unit configuration : configured) {
            if (post.isDominatedBy(store, configuration)) return true;
        }
        return false;
    }

    /**
     * The configuration value {@code value} is in {@code body}, or null:
     * through each local's one definition, casts, parses, views and clamps,
     * to a getter's or wrapper's return.
     *
     * @param through the sites of the definitions it passes, collected (the
     *                getter call's among them), or null
     */
    private ConfigValue valueOf(Value value, Body body, int depth,
                                Set<String> through) {
        if (value instanceof Local) {
            // A parameter is the caller's value, no configuration here.
            Unit definition = uniqueDefinitionUnit(body, (Local) value);
            if (!(definition instanceof AssignStmt)) return null;
            if (through != null) {
                through.add(SiteId.render(body.getMethod().getSignature(),
                        indexOf(body, definition)));
            }
            return valueOf(((AssignStmt) definition).getRightOp(), body,
                    depth, through);
        }
        if (value instanceof CastExpr) {
            return valueOf(((CastExpr) value).getOp(), body, depth, through);
        }
        if (!(value instanceof InvokeExpr)) return null;
        InvokeExpr invoke = (InvokeExpr) value;
        String callee = invoke.getMethodRef().getSignature();
        if (PARSES.contains(callee)) {
            return valueOf(invoke instanceof InstanceInvokeExpr
                    ? ((InstanceInvokeExpr) invoke).getBase()
                    : invoke.getArg(0), body, depth, through);
        }
        if (EQUALS.equals(callee)) {
            Value base = ((InstanceInvokeExpr) invoke).getBase();
            Value argument = invoke.getArg(0);
            String literal = literalString(base, body);
            Value viewed = argument;
            if (literal == null) {
                literal = literalString(argument, body);
                viewed = base;
            }
            ConfigValue raw = literal == null ? null
                    : valueOf(viewed, body, depth, through);
            return raw == null ? null : raw.viewed(literal);
        }
        Boolean floor = CLAMPS.get(callee);
        if (floor != null) {
            BigInteger first = literal(invoke.getArg(0));
            BigInteger second = literal(invoke.getArg(1));
            if ((first == null) == (second == null)) return null;
            ConfigValue raw = valueOf(invoke.getArg(first == null ? 0 : 1),
                    body, depth, through);
            return raw == null ? null : raw.clamped(new Clamp(floor,
                    first == null ? second : first));
        }
        Getter getter = getter(invoke.getMethodRef(), depth + 1);
        return getter == null ? null : called(getter, invoke, body);
    }

    /** What one call of a getter in {@code body} reads: its key, or the
     *  parameter of {@code body}'s method that states it, or neither; the
     *  shape the getter reads it in, and the default it names. */
    private static ConfigValue called(Getter getter, InvokeExpr invoke,
                                      Body body) {
        List<BigInteger> defaults = new ArrayList<>(getter.defaults);
        if (getter.defaultArg >= 0
                && getter.defaultArg < invoke.getArgCount()) {
            BigInteger fallback = literal(invoke.getArg(getter.defaultArg));
            if (fallback != null) defaults.add(fallback);
        }
        if (getter.key != null) {
            return new ConfigValue(getter.key, -1, getter.view,
                    getter.clamps, defaults);
        }
        Value key = getter.keyArg < invoke.getArgCount()
                ? invoke.getArg(getter.keyArg) : null;
        Unit definition = key instanceof Local
                ? uniqueDefinitionUnit(body, (Local) key) : null;
        if (definition instanceof AssignStmt) {
            key = ((AssignStmt) definition).getRightOp();
        }
        if (key instanceof StringConstant) {
            return new ConfigValue(((StringConstant) key).value, -1,
                    getter.view, getter.clamps, defaults);
        }
        int parameter = definition instanceof IdentityStmt
                && ((IdentityStmt) definition).getRightOp()
                instanceof ParameterRef ? ((ParameterRef) ((IdentityStmt)
                definition).getRightOp()).getIndex() : -1;
        return new ConfigValue(null, parameter, getter.view, getter.clamps,
                defaults);
    }

    /**
     * The getter {@code reference} calls: a JVM or catalog getter, on its
     * class or a subclass, or a wrapper of one; null for anything else.
     */
    private Getter getter(SootMethodRef reference, int depth) {
        String signature = reference.getSignature();
        Getter library = libraryGetter(reference);
        if (library != null) return library;
        if (getters.containsKey(signature)) return getters.get(signature);
        if (open.contains(signature) || depth >= MAX_DEPTH) return null;
        open.add(signature);
        Getter wrapper = wrapper(signature, depth);
        open.remove(signature);
        getters.put(signature, wrapper);
        return wrapper;
    }

    /** A JVM or catalog getter, on its class or a subclass; or null. */
    private static Getter libraryGetter(SootMethodRef reference) {
        String signature = reference.getSignature();
        for (Object[] jvm : JVM_GETTERS) {
            if (jvm[0].equals(signature)) {
                return new Getter((Integer) jvm[1], (Integer) jvm[2]);
            }
        }
        for (LibraryCatalog.ConfigSource row
                : LibraryCatalog.configSources()) {
            if (row.method.equals(signature) || inherits(reference,
                    row.method)) {
                return new Getter(row.keyArg, row.defaultArg);
            }
        }
        return null;
    }

    /** A wrapper: a method each of whose returns is a configuration value
     *  of one key in one shape, its key a literal or one of its String
     *  parameters. */
    private Getter wrapper(String signature, int depth) {
        SootMethod method = CausynthStaticFacts.method(signature);
        Body body = CausynthStaticFacts.activeBody(method);
        if (body == null) return null;
        ConfigValue returned = null;
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof ReturnStmt)) continue;
            ConfigValue value = valueOf(((ReturnStmt) unit).getOp(), body,
                    depth, null);
            if (value == null
                    || returned != null && !returned.sameShape(value)) {
                return null;
            }
            returned = returned == null ? value
                    : returned.withDefaults(value.defaults);
        }
        if (returned == null) return null;
        if (returned.key != null) {
            return new Getter(-1, -1, returned.key, returned.view,
                    returned.clamps, returned.defaults);
        }
        return returned.keyParam >= 0 && "java.lang.String".equals(
                method.getParameterType(returned.keyParam).toString())
                ? new Getter(returned.keyParam, -1, null, returned.view,
                returned.clamps, returned.defaults) : null;
    }

    /** Whether {@code reference} names {@code catalogMethod} on a subclass
     *  of its class: Hadoop's {@code HdfsConfiguration}. */
    private static boolean inherits(SootMethodRef reference,
                                    String catalogMethod) {
        int colon = catalogMethod.indexOf(": ");
        String owner = catalogMethod.substring(1, colon);
        String subSignature = catalogMethod.substring(colon + 2,
                catalogMethod.length() - 1);
        if (!subSignature.equals(reference.getSubSignature().toString())) {
            return false;
        }
        SootClass parent = Scene.v().getSootClassUnsafe(owner, false);
        SootClass child = reference.getDeclaringClass();
        if (parent == null || child == null || parent.equals(child)) {
            return false;
        }
        FastHierarchy hierarchy = Scene.v().getOrMakeFastHierarchy();
        return hierarchy.canStoreType(child.getType(), parent.getType());
    }

    /** The scene's reference of a callee signature, or null. */
    private static SootMethodRef reference(String signature) {
        SootMethod method = CausynthStaticFacts.method(signature);
        if (method != null) return method.makeRef();
        java.util.regex.Matcher parts = CausynthStaticFacts.METHOD_SIGNATURE
                .matcher(signature);
        if (!parts.matches()) return null;
        SootClass owner = Scene.v().getSootClassUnsafe(parts.group(1),
                false);
        if (owner == null) return null;
        List<Type> parameters = new ArrayList<>();
        if (!parts.group(4).trim().isEmpty()) {
            for (String parameter : parts.group(4).split(",")) {
                parameters.add(Scene.v().getTypeUnsafe(parameter.trim(),
                        true));
            }
        }
        Type returned = Scene.v().getTypeUnsafe(parts.group(2).trim(), true);
        if (returned == null || parameters.contains(null)) return null;
        return Scene.v().makeMethodRef(owner, parts.group(3), parameters,
                returned, false);
    }

    /** The invoke of {@code unit}, or null. */
    private static InvokeExpr invokeOf(Unit unit) {
        return unit instanceof soot.jimple.Stmt
                && ((soot.jimple.Stmt) unit).containsInvokeExpr()
                ? ((soot.jimple.Stmt) unit).getInvokeExpr() : null;
    }

    private static Unit unitAt(Body body, int unitIndex) {
        if (body == null || unitIndex < 0) return null;
        int index = 0;
        for (Unit unit : body.getUnits()) {
            if (index++ == unitIndex) return unit;
        }
        return null;
    }

    private static int indexOf(Body body, Unit target) {
        int index = 0;
        for (Unit unit : body.getUnits()) {
            if (unit == target) return index;
            index++;
        }
        return -1;
    }

    /** The one unit defining {@code local}, or null for none or two. */
    private static Unit uniqueDefinitionUnit(Body body, Local local) {
        Unit found = null;
        for (Unit unit : body.getUnits()) {
            for (soot.ValueBox box : unit.getDefBoxes()) {
                if (box.getValue() != local) continue;
                if (found != null) return null;
                found = unit;
            }
        }
        return found;
    }

    private static Value uniqueDefinition(Body body, Local local) {
        Unit unit = uniqueDefinitionUnit(body, local);
        return unit instanceof AssignStmt
                ? ((AssignStmt) unit).getRightOp() : null;
    }

    /** The String literal a value is, directly or as a local only one
     *  defines; or null. */
    private static String literalString(Value value, Body body) {
        if (value instanceof Local) value = uniqueDefinition(body,
                (Local) value);
        return value instanceof StringConstant
                ? ((StringConstant) value).value : null;
    }

    /** An integral constant's value, or null. */
    private static BigInteger literal(Value value) {
        if (value instanceof IntConstant) {
            return BigInteger.valueOf(((IntConstant) value).value);
        }
        if (value instanceof LongConstant) {
            return BigInteger.valueOf(((LongConstant) value).value);
        }
        return null;
    }

    /** A field's declared type. */
    private static String fieldType(String field) {
        SootField declared = Scene.v().grabField(field);
        return declared == null ? "" : declared.getType().toString();
    }

    /** Whether a cell is a field (a store's target). */
    private static boolean fieldCell(String cell) {
        return cell.startsWith("<") && cell.endsWith(">")
                && !cell.contains("(");
    }
}
