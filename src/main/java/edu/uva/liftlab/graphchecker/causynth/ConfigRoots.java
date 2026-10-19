package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.Validity;
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
import soot.jimple.GeExpr;
import soot.jimple.GotoStmt;
import soot.jimple.GtExpr;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.LeExpr;
import soot.jimple.LongConstant;
import soot.jimple.LookupSwitchStmt;
import soot.jimple.LtExpr;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.StringConstant;
import soot.jimple.TableSwitchStmt;
import soot.jimple.ThrowStmt;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.MHGDominatorsFinder;
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

final class ConfigRoots {
    static final String PREFIX = "CONFIG:";
    static final String VIEW = "==";
    static final String KEY_UNRESOLVED = "CONFIG_KEY_UNRESOLVED";
    static final String FIELD_OVERWRITTEN = "CONFIG_FIELD_OVERWRITTEN";
    static final String READ_CONCRETE = "CONFIG_READ_CONCRETE";
    private static final int MAX_DEPTH = 4;
    private static final int FLOWS = 8;

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

    static final class Source {
        final String sourceId;
        final String javaType;
        final String domainMin;
        final String domainMax;
        final Validity valid;

        private Source(String sourceId, String javaType, String domainMin,
                       String domainMax, Validity valid) {
            this.sourceId = sourceId;
            this.javaType = javaType;
            this.domainMin = domainMin;
            this.domainMax = domainMax;
            this.valid = valid;
        }
    }

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

    private static final class ConfigValue {
        final String key;
        final int keyParam;
        final String view;
        final List<Clamp> clamps;
        final List<BigInteger> defaults;
        final Validity valid;

        ConfigValue(String key, int keyParam, String view, List<Clamp> clamps,
                    List<BigInteger> defaults) {
            this(key, keyParam, view, clamps, defaults, Validity.ANY);
        }

        ConfigValue(String key, int keyParam, String view, List<Clamp> clamps,
                    List<BigInteger> defaults, Validity valid) {
            this.key = key;
            this.keyParam = keyParam;
            this.view = view;
            this.clamps = clamps;
            this.defaults = defaults;
            this.valid = valid;
        }

        boolean sameShape(ConfigValue other) {
            return other != null && keyParam == other.keyParam
                    && Objects.equals(key, other.key)
                    && Objects.equals(view, other.view)
                    && clamps.equals(other.clamps);
        }

        ConfigValue viewed(String literal) {
            if (view != null || !clamps.isEmpty()) return null;
            return new ConfigValue(key, keyParam, literal, clamps, defaults);
        }

        ConfigValue clamped(Clamp clamp) {
            if (view != null) return null;
            List<Clamp> through = new ArrayList<>(clamps);
            through.add(clamp);
            Validity mapped = valid == Validity.ANY ? valid : Validity.of(
                    valid.min() == null ? (clamp.floor ? clamp.bound : null)
                            : clamp.apply(valid.min()),
                    valid.max() == null ? (clamp.floor ? null : clamp.bound)
                            : clamp.apply(valid.max()), valid.by());
            return new ConfigValue(key, keyParam, view, through, defaults,
                    mapped);
        }

        ConfigValue merged(ConfigValue other) {
            List<BigInteger> all = new ArrayList<>(defaults);
            all.addAll(other.defaults);
            return new ConfigValue(key, keyParam, view, clamps, all,
                    valid.or(other.valid));
        }

        ConfigValue validated(Validity checked) {
            return new ConfigValue(key, keyParam, view, clamps, defaults,
                    valid.and(checked));
        }

        String sourceId() {
            return PREFIX + key + (view == null ? "" : VIEW + view);
        }
    }

    private static final class Getter {
        final int keyArg;
        final int defaultArg;
        final String key;
        final String view;
        final List<Clamp> clamps;
        final List<BigInteger> defaults;
        final Validity valid;

        Getter(int keyArg, int defaultArg) {
            this(keyArg, defaultArg, null, null,
                    Collections.<Clamp>emptyList(),
                    Collections.<BigInteger>emptyList(), Validity.ANY);
        }

        Getter(int keyArg, int defaultArg, String key, String view,
               List<Clamp> clamps, List<BigInteger> defaults,
               Validity valid) {
            this.keyArg = keyArg;
            this.defaultArg = defaultArg;
            this.key = key;
            this.view = view;
            this.clamps = clamps;
            this.defaults = defaults;
            this.valid = valid;
        }
    }

    private static final class FieldValue {
        final ConfigValue value;
        final Refusal refusal;

        FieldValue(ConfigValue value, Refusal refusal) {
            this.value = value;
            this.refusal = refusal;
        }
    }

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

    private static final class Shape {
        final String sourceId;
        final String javaType;
        final ConfigValue value;
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

        boolean takes(Read read) {
            return !field && javaType.equals(read.type)
                    && value.sameShape(read.value);
        }
    }

    private static final class Refusal {
        final String reason;
        final String method;
        final String siteId;
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
    private final Set<String> open = new HashSet<>();
    private final Map<String, Source> fields = new TreeMap<>();
    private final Map<String, Source> calls = new TreeMap<>();
    private final Set<String> configFields = new TreeSet<>();
    private final Set<String> configCallees = new TreeSet<>();
    private final List<Refusal> refusals = new ArrayList<>();
    private final Set<String> fieldReads = new HashSet<>();
    private final Map<String, Set<String>> fieldStoredReads = new HashMap<>();
    private final Map<String, Shape> shapes = new HashMap<>();
    private final Map<String, FieldValue> fieldValues = new HashMap<>();
    private Map<String, List<String>> fieldWriters =
            Collections.emptyMap();

    private ConfigRoots() {
    }

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
                    value.defaults, value.clamps, value.valid,
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
            Validity valid = null;
            for (Read read : shape.getValue()) {
                cells.add(text(read.edge.get("toCell")));
                defaults.addAll(read.value.defaults);
                valid = valid == null ? read.value.valid
                        : valid.or(read.value.valid);
            }
            Shape key = shape.getKey();
            Source source = roots.source(key.sourceId, key.javaType,
                    defaults, key.value.clamps, valid, cells, out,
                    guardsFrom);
            for (Read read : shape.getValue()) {
                roots.calls.put(callSite(read.method, read.unitIndex,
                        read.callee), source);
            }
        }
        return roots;
    }

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

    Source field(String field) {
        return fields.get(field);
    }

    Map<String, Source> fields() {
        return Collections.unmodifiableMap(fields);
    }

    Source call(String method, int unitIndex, String callee) {
        return calls.get(callSite(method, unitIndex, callee));
    }

    boolean configField(String field) {
        return configFields.contains(field);
    }

    Set<String> callees() {
        return Collections.unmodifiableSet(configCallees);
    }

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
            if (minted) {
                rows.add(StaticScopeMap.configKeyRow(shape.sourceId,
                        shape.at, concrete));
            }
        }
        return rows;
    }

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

    private Source source(String sourceId, String javaType,
                          List<BigInteger> defaults, List<Clamp> clamps,
                          Validity valid, Collection<String> cells,
                          Map<String, List<Map<String, Object>>> out,
                          Map<String, List<Map<String, Object>>> guardsFrom) {
        if ("boolean".equals(javaType)) {
            return new Source(sourceId, javaType, "", "", Validity.ANY);
        }
        List<BigInteger> spread = new ArrayList<>(defaults);
        for (BigInteger compared : comparedLiterals(cells, out, guardsFrom)) {
            spread.add(compared.subtract(BigInteger.ONE));
            spread.add(compared);
            spread.add(compared.add(BigInteger.ONE));
        }
        if (spread.isEmpty()) {
            return new Source(sourceId, javaType, "", "", valid);
        }
        BigInteger min = Collections.min(spread);
        BigInteger max = Collections.max(spread);
        for (Clamp clamp : clamps) {
            min = clamp.apply(min);
            max = clamp.apply(max);
        }
        return new Source(sourceId, javaType, min.toString(), max.toString(),
                valid);
    }

    private static final int THROW_REACH = 64;

    private static Validity validation(Body body, Set<Local> values,
                                       String method, Unit use) {
        Validity valid = Validity.ANY;
        if (body == null || values.isEmpty()) return valid;
        MHGDominatorsFinder<Unit> dominators =
                new MHGDominatorsFinder<>(new BriefUnitGraph(body));
        int index = 0;
        for (Unit unit : body.getUnits()) {
            int at = index++;
            if (!(unit instanceof IfStmt) || !(((IfStmt) unit).getCondition()
                    instanceof ConditionExpr)
                    || !dominators.isDominatedBy(use, unit)) {
                continue;
            }
            boolean takenThrows = onlyThrows(body,
                    ((IfStmt) unit).getTarget());
            boolean fallThrows = onlyThrows(body,
                    body.getUnits().getSuccOf(unit));
            if (takenThrows == fallThrows) continue;
            Validity admitted = admits((ConditionExpr) ((IfStmt) unit)
                    .getCondition(), values, body, !takenThrows,
                    SiteId.render(method, at));
            if (admitted != null) valid = valid.and(admitted);
        }
        return valid;
    }

    private static Validity admits(ConditionExpr condition, Set<Local> values,
                                   Body body, boolean holds, String by) {
        Value left = condition.getOp1();
        Value right = condition.getOp2();
        Value compared = left instanceof Local
                ? uniqueDefinition(body, (Local) left) : null;
        if ((compared instanceof CmpExpr || compared instanceof CmplExpr
                || compared instanceof CmpgExpr)
                && BigInteger.ZERO.equals(literal(right))) {
            left = ((soot.jimple.BinopExpr) compared).getOp1();
            right = ((soot.jimple.BinopExpr) compared).getOp2();
        }
        int relation;
        if (condition instanceof GtExpr) relation = 2;
        else if (condition instanceof GeExpr) relation = 1;
        else if (condition instanceof LtExpr) relation = -2;
        else if (condition instanceof LeExpr) relation = -1;
        else return null;
        BigInteger c;
        if (values.contains(left) && literal(right) != null) {
            c = literal(right);
        } else if (values.contains(right) && literal(left) != null) {
            c = literal(left);
            relation = -relation;
        } else {
            return null;
        }
        if (!holds) relation = relation == 2 ? -1 : relation == 1 ? -2
                : relation == -2 ? 1 : 2;
        switch (relation) {
            case 2: return Validity.of(c.add(BigInteger.ONE), null, by);
            case 1: return Validity.of(c, null, by);
            case -2: return Validity.of(null, c.subtract(BigInteger.ONE), by);
            default: return Validity.of(null, c, by);
        }
    }

    private static boolean onlyThrows(Body body, Unit start) {
        Unit at = start;
        for (int step = 0; step < THROW_REACH && at != null; step++) {
            if (at instanceof ThrowStmt) return true;
            if (at instanceof IfStmt || at instanceof TableSwitchStmt
                    || at instanceof LookupSwitchStmt
                    || at instanceof ReturnStmt
                    || at instanceof ReturnVoidStmt) {
                return false;
            }
            at = at instanceof GotoStmt ? ((GotoStmt) at).getTarget()
                    : body.getUnits().getSuccOf(at);
        }
        return false;
    }

    private static Set<Local> chain(Value value, Body body) {
        Set<Local> locals = new LinkedHashSet<>();
        Value at = value;
        for (int step = 0; step < 16 && at != null; step++) {
            if (at instanceof CastExpr) {
                at = ((CastExpr) at).getOp();
                continue;
            }
            if (at instanceof InvokeExpr && PARSES.contains(((InvokeExpr) at)
                    .getMethodRef().getSignature())) {
                InvokeExpr parse = (InvokeExpr) at;
                at = parse instanceof InstanceInvokeExpr
                        ? ((InstanceInvokeExpr) parse).getBase()
                        : parse.getArg(0);
                continue;
            }
            if (!(at instanceof Local) || !locals.add((Local) at)) break;
            at = uniqueDefinition(body, (Local) at);
        }
        return locals;
    }

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
                    if (fieldCell(to) || !seen.add(to)) continue;
                    next.add(to);
                }
            }
            frontier = next;
        }
        return new ArrayList<>(literals);
    }

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
            value = value.validated(validation(body, chain(right, body),
                    method, unit));
            stored = stored == null ? value : stored.merged(value);
            stores.computeIfAbsent(method, ignored -> new ArrayList<>())
                    .add(unit);
        }
        if (unresolved != null || stored != null) {
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

    private ConfigValue valueOf(Value value, Body body, int depth,
                                Set<String> through) {
        if (value instanceof Local) {
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
                    getter.clamps, defaults, getter.valid);
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
                    getter.view, getter.clamps, defaults, getter.valid);
        }
        int parameter = definition instanceof IdentityStmt
                && ((IdentityStmt) definition).getRightOp()
                instanceof ParameterRef ? ((ParameterRef) ((IdentityStmt)
                definition).getRightOp()).getIndex() : -1;
        return new ConfigValue(null, parameter, getter.view, getter.clamps,
                defaults, getter.valid);
    }

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
            value = value.validated(validation(body,
                    chain(((ReturnStmt) unit).getOp(), body), signature,
                    unit));
            returned = returned == null ? value : returned.merged(value);
        }
        if (returned == null) return null;
        if (returned.key != null) {
            return new Getter(-1, -1, returned.key, returned.view,
                    returned.clamps, returned.defaults, returned.valid);
        }
        return returned.keyParam >= 0 && "java.lang.String".equals(
                method.getParameterType(returned.keyParam).toString())
                ? new Getter(returned.keyParam, -1, null, returned.view,
                returned.clamps, returned.defaults, returned.valid) : null;
    }

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

    private static String literalString(Value value, Body body) {
        if (value instanceof Local) value = uniqueDefinition(body,
                (Local) value);
        return value instanceof StringConstant
                ? ((StringConstant) value).value : null;
    }

    private static BigInteger literal(Value value) {
        if (value instanceof IntConstant) {
            return BigInteger.valueOf(((IntConstant) value).value);
        }
        if (value instanceof LongConstant) {
            return BigInteger.valueOf(((LongConstant) value).value);
        }
        return null;
    }

    private static String fieldType(String field) {
        SootField declared = Scene.v().grabField(field);
        return declared == null ? "" : declared.getType().toString();
    }

    private static boolean fieldCell(String cell) {
        return cell.startsWith("<") && cell.endsWith(">")
                && !cell.contains("(");
    }
}
