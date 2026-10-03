package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.SiteId;
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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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
 *       ({@link #valueOf}) of one key -- a literal, or the wrapper's own
 *       String parameter -- followed {@value #MAX_DEPTH} deep: Solr's {@code
 *       "true".equals(getClusterProperty(LEGACY_CLOUD, "false"))};</li>
 *   <li>a FIELD: an integral or boolean instance field each writer of which
 *       ({@link StaticProgram#fieldWriters}, the whole analysed scope)
 *       stores a configuration value of one key -- a constant its own
 *       initializer stores first excepted --, as hdfs-17960's {@code
 *       SnapshotManager.snapshotDeletionOrdered} = {@code
 *       conf.getBoolean(DFS_NAMENODE_SNAPSHOT_DELETION_ORDERED, false)} in
 *       its constructor; or a field of a {@code CONFIG_FIELD_OWNER} class,
 *       which is its own key.</li>
 * </ul>
 * A configuration value is a getter's or wrapper's return through locals,
 * casts, a boolean view (a literal's {@code equals}, {@code
 * Boolean.parseBoolean}/{@code valueOf}), a parse, an unboxing, {@code trim}
 * and {@code Math.max}/{@code min} with a constant; arithmetic makes another
 * value.
 *
 * <p>The key is the key argument where it is a literal (javac inlines a
 * {@code static final String}), else the getter call's site; a source is
 * {@code CONFIG:<key>}.  One key is one root, minted in one shape: the
 * key's first field (by signature) where a field holds it, else each
 * primitive getter call the slice reads it at.  The VM names a field mint by
 * its owner's class, so a second field of one key would be a second symbol
 * of one root; it is read concretely instead (SYMBOL-SCOPE §7).</p>
 *
 * <p>An integral source's domain is the hull of its anchors: each getter's
 * literal default and {@code c - 1, c, c + 1} for each integral literal
 * {@code c} a branch compares its value with within {@value #FLOWS} flows
 * of the slice, never through a field; at {@code 0} or above where every
 * anchor is.  The mint adds the value it read ({@code runtime.RootMint}).</p>
 */
final class ConfigRoots {
    /** The prefix of every configuration source id. */
    static final String PREFIX = "CONFIG:";
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

    /** A configuration value's view: the same key under another type. */
    private static final Set<String> VIEWS = new LinkedHashSet<>(
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
    private static final Set<String> CLAMPS = new LinkedHashSet<>(
            Arrays.asList("<java.lang.Math: int max(int,int)>",
                    "<java.lang.Math: int min(int,int)>",
                    "<java.lang.Math: long max(long,long)>",
                    "<java.lang.Math: long min(long,long)>"));
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

        /** The key it is the configuration of. */
        String key() {
            return sourceId.substring(PREFIX.length());
        }
    }

    /** A getter: which argument is its key, which its default; or a
     *  wrapper of one with its key fixed. */
    private static final class Getter {
        final int keyArg;
        final int defaultArg;
        /** A wrapper's own key, or null when an argument states it. */
        final String key;
        final List<BigInteger> defaults;

        Getter(int keyArg, int defaultArg, String key,
               List<BigInteger> defaults) {
            this.keyArg = keyArg;
            this.defaultArg = defaultArg;
            this.key = key;
            this.defaults = defaults;
        }
    }

    /** A configuration value at one point of a body: its key, or the
     *  parameter that states it, and the defaults its getters name. */
    private static final class ConfigValue {
        final String key;
        final int keyParam;
        final List<BigInteger> defaults;

        ConfigValue(String key, int keyParam, List<BigInteger> defaults) {
            this.key = key;
            this.keyParam = keyParam;
            this.defaults = defaults;
        }

        boolean sameKey(ConfigValue other) {
            return other != null && keyParam == other.keyParam
                    && (key == null ? other.key == null
                    : key.equals(other.key));
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
        Map<String, List<String>> keyFields = new TreeMap<>();
        Map<String, List<BigInteger>> fieldDefaults = new HashMap<>();
        for (String field : readFields) {
            ConfigValue value = roots.fieldValue(field, fieldWriters);
            if (value == null) continue;
            roots.configFields.add(field);
            keyFields.computeIfAbsent(value.key,
                    ignored -> new ArrayList<>()).add(field);
            fieldDefaults.put(field, value.defaults);
        }
        for (Map.Entry<String, List<String>> key : keyFields.entrySet()) {
            String field = key.getValue().get(0);
            roots.fields.put(field, roots.source(key.getKey(),
                    fieldType(field), fieldDefaults.get(field),
                    Collections.singleton(field), out, guardsFrom));
        }
        Map<String, List<Map<String, Object>>> keyCalls = new TreeMap<>();
        Map<String, List<BigInteger>> callDefaults = new TreeMap<>();
        Map<String, String> callTypes = new HashMap<>();
        for (Map.Entry<String, List<Map<String, Object>>> callee
                : callSites.entrySet()) {
            SootMethodRef reference = reference(callee.getKey());
            if (reference == null) continue;
            Getter getter = roots.getter(reference, 0);
            if (getter == null) continue;
            roots.configCallees.add(callee.getKey());
            String type = reference.getReturnType().toString();
            for (Map<String, Object> edge : callee.getValue()) {
                String method = text(edge.get("method"));
                int unitIndex = MapFields.number(edge.get("unitIndex"), -1);
                Body body = CausynthStaticFacts.activeBody(
                        CausynthStaticFacts.method(method));
                InvokeExpr invoke = invokeOf(unitAt(body, unitIndex));
                if (invoke == null) continue;
                ConfigValue value = called(getter, invoke, body,
                        SiteId.render(method, unitIndex));
                if (value.key == null || keyFields.containsKey(value.key)
                        || !MINTABLE.contains(type)) {
                    continue;
                }
                keyCalls.computeIfAbsent(value.key,
                        ignored -> new ArrayList<>()).add(edge);
                callDefaults.computeIfAbsent(value.key,
                        ignored -> new ArrayList<>()).addAll(value.defaults);
                callTypes.putIfAbsent(value.key, type);
            }
        }
        for (Map.Entry<String, List<Map<String, Object>>> key
                : keyCalls.entrySet()) {
            Set<String> cells = new LinkedHashSet<>();
            for (Map<String, Object> edge : key.getValue()) {
                cells.add(text(edge.get("toCell")));
            }
            Source source = roots.source(key.getKey(),
                    callTypes.get(key.getKey()),
                    callDefaults.get(key.getKey()), cells, out, guardsFrom);
            for (Map<String, Object> edge : key.getValue()) {
                roots.calls.put(callSite(text(edge.get("method")),
                        MapFields.number(edge.get("unitIndex"), -1),
                        text(edge.get("invoke"))), source);
            }
        }
        return roots;
    }

    /** The same recognition, minting only these roots ({@link
     *  RootDemand#configSources}). */
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

    /** Whether a callee of the slice is a configuration getter or a
     *  wrapper of one. */
    boolean configCallee(String callee) {
        return configCallees.contains(callee);
    }

    private static String callSite(String method, int unitIndex,
                                   String callee) {
        return SiteId.render(method, unitIndex) + "|" + callee;
    }

    /** A root of {@code key} read at {@code cells}, its domain from its
     *  defaults and the literals the slice compares those cells with. */
    private Source source(String key, String javaType,
                          List<BigInteger> defaults, Collection<String> cells,
                          Map<String, List<Map<String, Object>>> out,
                          Map<String, List<Map<String, Object>>> guardsFrom) {
        if ("boolean".equals(javaType)) {
            return new Source(PREFIX + key, javaType, "", "");
        }
        List<BigInteger> anchors = new ArrayList<>(defaults);
        List<BigInteger> spread = new ArrayList<>(defaults);
        for (BigInteger compared : comparedLiterals(cells, out, guardsFrom)) {
            anchors.add(compared);
            spread.add(compared.subtract(BigInteger.ONE));
            spread.add(compared);
            spread.add(compared.add(BigInteger.ONE));
        }
        if (spread.isEmpty()) {
            return new Source(PREFIX + key, javaType, "", "");
        }
        BigInteger min = Collections.min(spread);
        if (Collections.min(anchors).signum() >= 0) {
            min = min.max(BigInteger.ZERO);
        }
        return new Source(PREFIX + key, javaType, min.toString(),
                Collections.max(spread).toString());
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

    /** The configuration value {@code field} holds, or null: an integral or
     *  boolean instance field each writer stores one key in, or a field of
     *  a configuration class. */
    private ConfigValue fieldValue(String field,
                                   Map<String, List<String>> fieldWriters) {
        SootField declared = Scene.v().grabField(field);
        if (declared == null || declared.isStatic()
                || !MINTABLE.contains(declared.getType().toString())) {
            return null;
        }
        if (LibraryCatalog.configFieldOwners().contains(
                declared.getDeclaringClass().getName())) {
            return new ConfigValue(field, -1,
                    Collections.<BigInteger>emptyList());
        }
        List<String> writers = fieldWriters.getOrDefault(field,
                Collections.<String>emptyList());
        ConfigValue stored = null;
        List<BigInteger> defaults = new ArrayList<>();
        Set<String> storing = new HashSet<>();
        Set<String> initializing = new HashSet<>();
        for (String writer : writers) {
            String method = SiteId.methodOf(writer);
            Body body = CausynthStaticFacts.activeBody(
                    CausynthStaticFacts.method(method));
            Unit unit = unitAt(body, SiteId.unitIndexOf(writer));
            if (!(unit instanceof AssignStmt)
                    || !(((AssignStmt) unit).getLeftOp() instanceof FieldRef)) {
                return null;
            }
            Value right = ((AssignStmt) unit).getRightOp();
            if (right instanceof soot.jimple.Constant) {
                // An initializer, if its method stores the configuration.
                initializing.add(method);
                continue;
            }
            ConfigValue value = valueOf(right, body, writer, 0);
            if (value == null || value.key == null
                    || stored != null && !stored.sameKey(value)) {
                return null;
            }
            stored = value;
            storing.add(method);
            defaults.addAll(value.defaults);
        }
        if (stored == null || !storing.containsAll(initializing)) return null;
        return new ConfigValue(stored.key, -1, defaults);
    }

    /**
     * The configuration value {@code value} is in {@code body}, or null:
     * through each local's one definition, casts, views and clamps, to a
     * getter's or wrapper's return.
     *
     * @param site the site of the statement {@code value} is in: the key of
     *             a getter whose key argument states none
     */
    private ConfigValue valueOf(Value value, Body body, String site,
                                int depth) {
        if (value instanceof Local) {
            // A parameter is the caller's value, no configuration here.
            Unit definition = uniqueDefinitionUnit(body, (Local) value);
            if (!(definition instanceof AssignStmt)) return null;
            return valueOf(((AssignStmt) definition).getRightOp(), body,
                    SiteId.render(body.getMethod().getSignature(),
                            indexOf(body, definition)), depth);
        }
        if (value instanceof CastExpr) {
            return valueOf(((CastExpr) value).getOp(), body, site, depth);
        }
        if (!(value instanceof InvokeExpr)) return null;
        InvokeExpr invoke = (InvokeExpr) value;
        String callee = invoke.getMethodRef().getSignature();
        if (VIEWS.contains(callee)) {
            return valueOf(invoke instanceof InstanceInvokeExpr
                    ? ((InstanceInvokeExpr) invoke).getBase()
                    : invoke.getArg(0), body, site, depth);
        }
        if (EQUALS.equals(callee)) {
            Value base = ((InstanceInvokeExpr) invoke).getBase();
            Value argument = invoke.getArg(0);
            if (literalString(base, body)) {
                return valueOf(argument, body, site, depth);
            }
            return literalString(argument, body)
                    ? valueOf(base, body, site, depth) : null;
        }
        if (CLAMPS.contains(callee)) {
            boolean first = literal(invoke.getArg(0)) != null;
            if (first == (literal(invoke.getArg(1)) != null)) return null;
            return valueOf(invoke.getArg(first ? 1 : 0), body, site, depth);
        }
        Getter getter = getter(invoke.getMethodRef(), depth + 1);
        return getter == null ? null : called(getter, invoke, body, site);
    }

    /** What one call of a getter in {@code body} reads: its key, or the
     *  parameter of {@code body}'s method that states it, and the default
     *  it names. */
    private static ConfigValue called(Getter getter, InvokeExpr invoke,
                                      Body body, String site) {
        List<BigInteger> defaults = new ArrayList<>(getter.defaults);
        if (getter.defaultArg >= 0
                && getter.defaultArg < invoke.getArgCount()) {
            BigInteger fallback = literal(invoke.getArg(getter.defaultArg));
            if (fallback != null) defaults.add(fallback);
        }
        if (getter.key != null) {
            return new ConfigValue(getter.key, -1, defaults);
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
                    defaults);
        }
        if (definition instanceof IdentityStmt && ((IdentityStmt) definition)
                .getRightOp() instanceof ParameterRef) {
            return new ConfigValue(null, ((ParameterRef) ((IdentityStmt)
                    definition).getRightOp()).getIndex(), defaults);
        }
        return new ConfigValue(site, -1, defaults);
    }

    /**
     * The getter {@code reference} calls: a JVM or catalog getter, on its
     * class or a subclass, or a wrapper of one; null for anything else.
     */
    private Getter getter(SootMethodRef reference, int depth) {
        String signature = reference.getSignature();
        for (Object[] jvm : JVM_GETTERS) {
            if (jvm[0].equals(signature)) {
                return new Getter((Integer) jvm[1], (Integer) jvm[2], null,
                        Collections.<BigInteger>emptyList());
            }
        }
        for (LibraryCatalog.ConfigSource row
                : LibraryCatalog.configSources()) {
            if (row.method.equals(signature) || inherits(reference,
                    row.method)) {
                return new Getter(row.keyArg, row.defaultArg, null,
                        Collections.<BigInteger>emptyList());
            }
        }
        if (getters.containsKey(signature)) return getters.get(signature);
        if (open.contains(signature) || depth >= MAX_DEPTH) return null;
        open.add(signature);
        Getter wrapper = wrapper(signature, depth);
        open.remove(signature);
        getters.put(signature, wrapper);
        return wrapper;
    }

    /** A wrapper: a method each of whose returns is a configuration value
     *  of one key, a literal or one of its String parameters. */
    private Getter wrapper(String signature, int depth) {
        SootMethod method = CausynthStaticFacts.method(signature);
        Body body = CausynthStaticFacts.activeBody(method);
        if (body == null) return null;
        ConfigValue returned = null;
        List<BigInteger> defaults = new ArrayList<>();
        int index = 0;
        for (Unit unit : body.getUnits()) {
            if (unit instanceof ReturnStmt) {
                ConfigValue value = valueOf(((ReturnStmt) unit).getOp(),
                        body, SiteId.render(signature, index), depth);
                if (value == null
                        || returned != null && !returned.sameKey(value)) {
                    return null;
                }
                returned = value;
                defaults.addAll(value.defaults);
            }
            index++;
        }
        if (returned == null) return null;
        if (returned.key != null) {
            return new Getter(-1, -1, returned.key, defaults);
        }
        return "java.lang.String".equals(method.getParameterType(
                returned.keyParam).toString())
                ? new Getter(returned.keyParam, -1, null, defaults) : null;
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

    /** Whether a value is a String literal, or a local only one defines. */
    private static boolean literalString(Value value, Body body) {
        if (value instanceof Local) value = uniqueDefinition(body,
                (Local) value);
        return value instanceof StringConstant;
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
