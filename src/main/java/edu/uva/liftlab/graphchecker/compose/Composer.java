package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Term;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.explore.Corpus;
import edu.uva.liftlab.graphchecker.explore.Moved;
import edu.uva.liftlab.graphchecker.explore.SlotTable;
import edu.uva.liftlab.graphchecker.contract.ContentPort;
import edu.uva.liftlab.graphchecker.contract.Family;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.HeapWatch;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.PathEntry;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootDomain;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.smt.ExpressionWalk;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.smt.VmRows;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.runtime.Confirmation;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.TimeUnit;
import java.util.function.DoubleSupplier;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.smtLiteral;
import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.smtName;
import static edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.integralLiteral;

public final class Composer {

    public static final class Valuation {
        private final int ordinal;
        private final Map<String, String> assignment;
        private final Map<String, String> moved;
        private final List<String> assertions;

        private Valuation(int ordinal, Map<String, String> assignment,
                          Map<String, String> moved,
                          List<String> assertions) {
            this.ordinal = ordinal;
            this.assignment = Collections.unmodifiableMap(assignment);
            this.moved = Collections.unmodifiableMap(moved);
            this.assertions = Collections.unmodifiableList(assertions);
        }

        public int ordinal() {
            return ordinal;
        }

        public Map<String, String> assignment() {
            return assignment;
        }

        public Map<String, String> moved() {
            return moved;
        }

        public List<String> assertions() {
            return assertions;
        }

        @Override
        public String toString() {
            return "valuation " + ordinal
                    + (moved.isEmpty() ? " (recorded)" : " " + moved);
        }
    }

    public static final class Disjunct {
        private final Corpus.RecordedPath path;
        private final String selector;
        private final String fatal;
        private final String withoutFatalArm;
        private final boolean fatalObserved;
        private final Set<String> interactionIds;
        private final Set<String> restsOn;
        private final long cutoff;

        private Disjunct(Corpus.RecordedPath path, String selector,
                         String fatal, String withoutFatalArm,
                         boolean fatalObserved, Set<String> interactionIds,
                         Set<String> restsOn, long cutoff) {
            this.path = path;
            this.selector = selector;
            this.fatal = fatal;
            this.withoutFatalArm = withoutFatalArm;
            this.fatalObserved = fatalObserved;
            this.interactionIds = Collections.unmodifiableSet(interactionIds);
            this.restsOn = Collections.unmodifiableSet(restsOn);
            this.cutoff = cutoff;
        }

        public Corpus.RecordedPath path() {
            return path;
        }

        public String selector() {
            return selector;
        }

        public boolean fatalObserved() {
            return fatalObserved;
        }

        public Set<String> interactionIds() {
            return interactionIds;
        }

        public Set<String> restsOn() {
            return restsOn;
        }

        public long cutoff() {
            return cutoff;
        }
    }

    public static final class Composition {
        private final List<Concrete> concrete;
        private final Map<String, RootMintRow> declaredRoots;
        private final Map<String, String> recordedValues;
        private final OccurrenceAddress anchor;
        private final String body;
        private Cone cone;
        private final List<Disjunct> disjuncts;
        private final List<PathEntry> paths;
        private final List<Family> families;
        private final List<RootDomain> roots;
        private final Map<String, RootCategory> categories;
        private final Map<String, List<String>> unplantedReads;
        private final List<Valuation> valuations;
        private final List<GapRow> gaps;
        private final List<String> clockCells;
        private final Map<String, Long> clockReadings;
        private final Map<String, Long> clockNanos;
        private final Map<String, String> clockBefore;
        private final Map<String, Set<String>> unattestedRoots;
        private final Map<String, List<String>> observedReads;
        private final Map<String, List<String>> observedArrivals;
        private final Map<String, List<String>> heldArrivals;
        private final Map<String, Endpoint> openArrivals;
        private final Map<String, ComposedFamilies.ArmChoice> armChoices;
        private final Map<String, Refutations.Refuted> refutations;
        private final List<JsonObject> refusedPaths;
        private final Map<String, List<String>> ownArms;
        private final Map<String, List<String>> recordedAtPlants;
        private final Map<String, Map<String, List<String>>> worldArms;
        private final String seedSessionId;
        private final Corpus corpus;
        private final Map<String, String> clockRootReadings;
        private final int[] commandEnds;
        private final String[] commandGuards;
        private final boolean[] commandRefuted;
        private int[][] commandRoots;
        private List<String> rootNames;
        private final Map<String, Set<String>> pathRoots =
                new HashMap<String, Set<String>>();

        private Composition(Composer composed, String body,
                            List<Disjunct> disjuncts, List<PathEntry> paths,
                            List<Valuation> valuations,
                            List<String> clockCells,
                            Map<String, Long> clockReadings,
                            Map<String, Long> clockNanos,
                            Map<String, String> clockBefore) {
            this.anchor = composed.anchor;
            this.body = body;
            this.disjuncts = Collections.unmodifiableList(disjuncts);
            this.paths = Collections.unmodifiableList(paths);
            this.families = Collections.unmodifiableList(
                    new ArrayList<Family>(composed.families.values()));
            this.roots = Collections.unmodifiableList(
                    new ArrayList<RootDomain>(composed.roots.values()));
            Map<String, RootCategory> categories =
                    new LinkedHashMap<String, RootCategory>();
            for (Map.Entry<String, List<RootMintRow>> root
                    : composed.corpus.roots().entrySet()) {
                categories.put(root.getKey(),
                        root.getValue().get(0).category());
            }
            this.categories = Collections.unmodifiableMap(categories);
            Map<String, List<String>> unplanted =
                    new LinkedHashMap<String, List<String>>();
            for (Map.Entry<String, RootCategory> root
                    : categories.entrySet()) {
                List<String> reads = composed.scope
                        .concreteConfigurationReads(root.getKey());
                if (root.getValue() == RootCategory.CONFIG
                        && !reads.isEmpty()) {
                    unplanted.put(root.getKey(), reads);
                }
            }
            this.unplantedReads = Collections.unmodifiableMap(unplanted);
            this.valuations = Collections.unmodifiableList(valuations);
            this.gaps = Collections.unmodifiableList(composed.gaps);
            this.clockCells = Collections.unmodifiableList(clockCells);
            this.clockReadings =
                    Collections.unmodifiableMap(clockReadings);
            this.clockNanos = Collections.unmodifiableMap(clockNanos);
            this.clockBefore = Collections.unmodifiableMap(clockBefore);
            this.unattestedRoots =
                    Collections.unmodifiableMap(composed.unattestedRoots);
            this.observedReads =
                    Collections.unmodifiableMap(composed.observedReads);
            this.observedArrivals =
                    Collections.unmodifiableMap(composed.observedArrivals);
            this.heldArrivals =
                    Collections.unmodifiableMap(composed.heldArrivals);
            this.openArrivals = Collections.unmodifiableMap(
                    new LinkedHashMap<String, Endpoint>(
                            composed.openArrivals));
            this.armChoices = composed.composedFamilies.armChoices();
            this.refutations = Collections.unmodifiableMap(
                    new LinkedHashMap<String, Refutations.Refuted>(
                            composed.refutationNames));
            this.refusedPaths = Collections.unmodifiableList(
                    new ArrayList<JsonObject>(composed.refusedPaths));
            this.concrete = Collections.unmodifiableList(
                    new ArrayList<Concrete>(composed.concrete.values()));
            this.declaredRoots = Collections.unmodifiableMap(
                    new LinkedHashMap<String, RootMintRow>(
                            composed.declaredRoots));
            Map<String, String> recordedValues =
                    new LinkedHashMap<String, String>();
            for (String rootId : declaredRoots.keySet()) {
                recordedValues.put(rootId,
                        composed.roots.get(rootId).recordedValue());
            }
            this.recordedValues = Collections.unmodifiableMap(recordedValues);
            this.ownArms = composed.composedFamilies.ownArms();
            this.recordedAtPlants =
                    composed.composedFamilies.recordedAtPlants();
            this.worldArms = composed.composedFamilies.worldArms();
            this.seedSessionId = composed.seed();
            this.corpus = composed.corpus;
            Map<String, String> readings = new LinkedHashMap<String, String>();
            for (RootDomain root : roots) {
                if (root.kind() == RootKind.CLOCK) {
                    readings.put(root.rootId(), root.recordedValue());
                }
            }
            this.clockRootReadings = Collections.unmodifiableMap(readings);
            List<Integer> ends = new ArrayList<Integer>();
            List<String> guards = new ArrayList<String>();
            commands(body, new LinkedHashSet<String>(
                    Composer.selectors(disjuncts)), ends, guards);
            this.commandEnds = new int[ends.size()];
            this.commandRefuted = new boolean[ends.size()];
            int start = 0;
            for (int index = 0; index < ends.size(); index++) {
                this.commandEnds[index] = ends.get(index);
                this.commandRefuted[index] = refutation(body, start,
                        commandEnds[index]);
                start = commandEnds[index];
            }
            this.commandGuards = guards.toArray(new String[0]);
        }

        public OccurrenceAddress anchor() {
            return anchor;
        }

        public String body() {
            return body;
        }

        public ArtifactIO.Body query(List<String> assertions) {
            List<String> legal = legal(assertions);
            return output -> {
                output.write(body);
                for (String assertion : legal) output.write(assertion);
            };
        }

        public ArtifactIO.Body sharedQuery() {
            return output -> {
                int start = 0;
                for (int index = 0; index < commandEnds.length; index++) {
                    if (commandGuards[index] == null
                            && !commandRefuted[index]) {
                        output.write(body, start, commandEnds[index] - start);
                    }
                    start = commandEnds[index];
                }
                output.write("\n");
            };
        }

        public ArtifactIO.Body scopeQuery(String selector,
                                          List<String> assertions) {
            List<String> legal = legal(assertions);
            legal.add(0, "\n(assert " + selector + ")\n");
            return output -> {
                int start = 0;
                for (int index = 0; index < commandEnds.length; index++) {
                    String guard = commandGuards[index];
                    if (guard == null ? commandRefuted[index]
                            : guard.equals(selector)) {
                        output.write(body, start, commandEnds[index] - start);
                    }
                    start = commandEnds[index];
                }
                for (String assertion : legal) output.write(assertion);
            };
        }

        public ArtifactIO.Body scopeWithoutFatalArm(String selector) {
            Disjunct disjunct = bySelector(selector);
            String own = "\n(assert " + SmtNames.legalSymbols(
                    disjunct.withoutFatalArm) + ")\n";
            String named = ":named " + disjunct.fatal + "))";
            return output -> {
                int start = 0;
                for (int index = 0; index < commandEnds.length; index++) {
                    int end = commandEnds[index];
                    if (selector.equals(commandGuards[index])
                            && !commandRefuted[index]) {
                        if (body.startsWith(named, end - named.length())) {
                            output.write(own);
                        } else {
                            output.write(body, start, end - start);
                        }
                    }
                    start = end;
                }
                output.write("\n(assert " + selector + ")\n");
            };
        }

        private static boolean refutation(String body, int start, int end) {
            String tail = body.substring(Math.max(start, end - 64), end);
            return tail.contains(":named " + REFUTED_CLAIM);
        }

        public Set<String> rootsOf(String selector) {
            synchronized (pathRoots) {
                Set<String> known = pathRoots.get(selector);
                if (known != null) return known;
            }
            int[][] roots = commandRoots();
            Set<Integer> named = new HashSet<Integer>();
            for (int index = 0; index < roots.length; index++) {
                if (roots[index] != null
                        && selector.equals(commandGuards[index])) {
                    for (int root : roots[index]) named.add(root);
                }
            }
            boolean grew = !named.isEmpty();
            while (grew) {
                grew = false;
                for (int index = 0; index < roots.length; index++) {
                    if (roots[index] == null || roots[index].length < 2
                            || commandGuards[index] != null) {
                        continue;
                    }
                    boolean touches = false;
                    for (int root : roots[index]) {
                        touches |= named.contains(root);
                    }
                    if (!touches) continue;
                    for (int root : roots[index]) grew |= named.add(root);
                }
            }
            Set<String> symbols = new HashSet<String>();
            for (int root : named) symbols.add(rootNames.get(root));
            Set<String> found = Collections.unmodifiableSet(symbols);
            synchronized (pathRoots) {
                pathRoots.put(selector, found);
            }
            return found;
        }

        private synchronized int[][] commandRoots() {
            if (commandRoots != null) return commandRoots;
            Map<String, Integer> byLegal = new HashMap<String, Integer>();
            List<String> names = new ArrayList<String>();
            Set<Integer> lengths = new HashSet<Integer>();
            for (RootMintRow row : declaredRoots.values()) {
                String legal = SmtNames.legalSymbols(row.symbol());
                if (byLegal.containsKey(legal)) continue;
                byLegal.put(legal, names.size());
                names.add(row.symbol());
                lengths.add(legal.length());
            }
            int[][] found = new int[commandEnds.length][];
            Set<Integer> here = new TreeSet<Integer>();
            int command = 0;
            int at = 0;
            int end = body.length();
            while (at < end) {
                while (command < commandEnds.length
                        && at >= commandEnds[command]) {
                    found[command++] = indices(here);
                }
                char c = body.charAt(at);
                if (c == ';') {
                    int line = body.indexOf('\n', at);
                    at = line < 0 ? end : line + 1;
                } else if (c == '"') {
                    at++;
                    while (at < end) {
                        if (body.charAt(at) == '"') {
                            if (at + 1 < end && body.charAt(at + 1) == '"') {
                                at += 2;
                                continue;
                            }
                            at++;
                            break;
                        }
                        at++;
                    }
                } else if (c == '|' || simpleSymbolChar(c)) {
                    int start = at;
                    if (c == '|') {
                        int close = body.indexOf('|', at + 1);
                        at = close < 0 ? end : close + 1;
                    } else {
                        while (at < end && simpleSymbolChar(body.charAt(at))) {
                            at++;
                        }
                    }
                    if (lengths.contains(at - start)) {
                        Integer root = byLegal.get(body.substring(start, at));
                        if (root != null) here.add(root);
                    }
                } else {
                    at++;
                }
            }
            while (command < commandEnds.length) {
                found[command++] = indices(here);
            }
            rootNames = names;
            commandRoots = found;
            return found;
        }

        private static int[] indices(Set<Integer> here) {
            if (here.isEmpty()) return null;
            int[] indices = new int[here.size()];
            int at = 0;
            for (int index : here) indices[at++] = index;
            here.clear();
            return indices;
        }

        private static boolean simpleSymbolChar(char c) {
            return Character.isLetterOrDigit(c) || "~!@$%^&*_-+=<>.?/"
                    .indexOf(c) >= 0;
        }

        private static List<String> legal(List<String> assertions) {
            List<String> legal = new ArrayList<String>();
            if (assertions == null) return legal;
            for (String assertion : assertions) {
                if (assertion == null || assertion.isEmpty()) continue;
                legal.add(SmtNames.legalSymbols(assertion) + "\n");
            }
            return legal;
        }

        private static void commands(String body, Set<String> selectors,
                                     List<Integer> ends, List<String> guards) {
            int start = 0;
            int depth = 0;
            int index = 0;
            while (index < body.length()) {
                char at = body.charAt(index);
                if (at == '|') {
                    int close = body.indexOf('|', index + 1);
                    index = close < 0 ? body.length() : close + 1;
                    continue;
                }
                if (at == '"') {
                    int close = index + 1;
                    while (close < body.length()) {
                        if (body.charAt(close) == '"') {
                            if (close + 1 < body.length()
                                    && body.charAt(close + 1) == '"') {
                                close += 2;
                                continue;
                            }
                            break;
                        }
                        close++;
                    }
                    index = close + 1;
                    continue;
                }
                if (at == ';') {
                    int close = body.indexOf('\n', index);
                    index = close < 0 ? body.length() : close;
                    continue;
                }
                if (at == '(') depth++;
                if (at == ')' && --depth == 0) {
                    int from = start;
                    while (Character.isWhitespace(body.charAt(from))) from++;
                    ends.add(index + 1);
                    guards.add(guard(body.substring(from,
                            Math.min(index + 1, from + GUARD_PREFIX)),
                            selectors));
                    start = index + 1;
                }
                index++;
            }
            if (start < body.length()) {
                ends.add(body.length());
                guards.add(null);
            }
        }

        private static final int GUARD_PREFIX = 256;

        private static String guard(String command, Set<String> selectors) {
            String rest = command.startsWith("(assert (! (=> ")
                    ? command.substring("(assert (! (=> ".length())
                    : command.startsWith("(assert (=> ")
                    ? command.substring("(assert (=> ".length()) : null;
            if (rest == null) return null;
            int end = rest.indexOf(' ');
            String token = end < 0 ? rest : rest.substring(0, end);
            return selectors.contains(token) ? token : null;
        }

        public List<Disjunct> disjuncts() {
            return disjuncts;
        }

        public List<PathEntry> paths() {
            return paths;
        }

        public List<Family> families() {
            return families;
        }

        public List<Concrete> concrete() {
            return concrete;
        }

        public List<JsonObject> openChain(ClaimPolicy.Outcome witness) {
            List<JsonObject> open = new ArrayList<JsonObject>();
            if (witness != null) {
                if (witness.selected() != null) {
                    links(witness.selected(),
                            witness.selectedArms().keySet(), open);
                }
                return open;
            }
            for (Disjunct path : disjuncts) {
                links(path, Collections.<String>emptySet(), open);
            }
            return open;
        }

        public List<JsonObject> offWitness(ClaimPolicy.Outcome witness) {
            List<JsonObject> open = new ArrayList<JsonObject>();
            for (Disjunct path : disjuncts) {
                if (witness != null && path == witness.selected()) continue;
                links(path, Collections.<String>emptySet(), open);
            }
            return open;
        }

        private synchronized Cone cone() {
            if (cone == null) cone = new Cone(body);
            return cone;
        }

        private void links(Disjunct path, Set<String> arms,
                           List<JsonObject> open) {
            for (String symbol : cone().unbound(path.selector(),
                    path.path().pathId, arms, concrete)) {
                Endpoint producer = openArrivals.get(
                        SmtNames.legalSymbols(symbol));
                JsonObject row = new JsonObject();
                row.addProperty("symbol", symbol);
                row.addProperty("pathId", path.path().pathId);
                row.addProperty("producer", producer == null ? ""
                        : producer.occurrence().render());
                row.addProperty("producerEndpointId",
                        producer == null ? "" : producer.id());
                open.add(row);
            }
        }

        public List<RootDomain> roots() {
            return roots;
        }

        public RootCategory categoryOf(String moved) {
            return clockCells.contains(moved) ? RootCategory.CLOCK
                    : categories.get(moved);
        }

        public boolean configurationOnly(Collection<String> moved) {
            return Composer.configurationOnly(moved, this::categoryOf);
        }

        public Map<String, List<String>> unplanted(Collection<String> moved) {
            Map<String, List<String>> found =
                    new LinkedHashMap<String, List<String>>();
            for (String key : moved) {
                List<String> reads = unplantedReads.get(key);
                if (reads != null) found.put(key, reads);
            }
            return found;
        }

        public List<Valuation> valuations() {
            return valuations;
        }

        public List<GapRow> gaps() {
            return gaps;
        }

        public List<String> clockCells() {
            return clockCells;
        }

        public List<String> rootSymbols() {
            List<String> symbols = new ArrayList<String>();
            for (RootMintRow row : declaredRoots.values()) {
                symbols.add(SmtNames.legalSymbols(row.symbol()));
            }
            return symbols;
        }

        public Valuation free(int ordinal) {
            return new Valuation(ordinal, recordedValues,
                    Collections.<String, String>emptyMap(),
                    Collections.<String>emptyList());
        }

        public Valuation modelValuation(int ordinal,
                                        Map<String, String> model) {
            Map<String, String> assignment =
                    new LinkedHashMap<String, String>();
            Map<String, String> moved = new LinkedHashMap<String, String>();
            List<String> assertions = new ArrayList<String>();
            for (Map.Entry<String, RootMintRow> root
                    : declaredRoots.entrySet()) {
                String recorded = recordedValues.get(root.getKey());
                String value = modelValue(model.get(
                        SmtNames.legalSymbols(root.getValue().symbol())));
                if (value.isEmpty()) value = recorded;
                assignment.put(root.getKey(), value);
                if (!value.equals(recorded)) moved.put(root.getKey(), value);
                String literal = smtLiteral(value, sortOf(root.getValue()));
                if (literal.isEmpty()) continue;
                assertions.add("(assert (! (= " + root.getValue().symbol()
                        + " " + literal + ") :named " + VALUATION_PIN
                        + smtName(root.getValue().symbol()) + "))");
            }
            return new Valuation(ordinal, assignment, moved, assertions);
        }

        private static String modelValue(String model) {
            if (model == null) return "";
            String text = model.trim();
            if (text.startsWith("(-") && text.endsWith(")")) {
                return "-" + text.substring(2, text.length() - 1).trim();
            }
            return text;
        }

        public Map<String, Long> clockReadings() {
            return clockReadings;
        }

        public Map<String, Long> clockNanos() {
            return clockNanos;
        }

        public Map<String, String> clockBefore() {
            return clockBefore;
        }

        public Map<String, Set<String>> unattestedRoots() {
            return unattestedRoots;
        }

        public List<String> ownRun(String selector) {
            List<String> own = new ArrayList<String>();
            Disjunct disjunct = bySelector(selector);
            if (disjunct == null) return own;
            List<String> arms = ownArms.get(selector);
            if (arms != null) own.addAll(arms);
            List<String> reads = observedReads.get(disjunct.path().pathId);
            if (reads != null) own.addAll(reads);
            return asserted(own);
        }

        public List<String> observedReads(String pathId) {
            return asserted(observedReads.get(pathId));
        }

        public List<String> repaired(String selector,
                                     Collection<String> taken) {
            Set<String> own = new LinkedHashSet<String>();
            for (Map<String, List<String>> owned
                    : Arrays.asList(ownArms, recordedAtPlants)) {
                List<String> arms = owned.get(selector);
                if (arms != null) own.addAll(arms);
            }
            Disjunct disjunct = bySelector(selector);
            List<String> reads = disjunct == null ? null
                    : observedReads.get(disjunct.path().pathId);
            if (reads != null) own.addAll(reads);
            List<String> repaired = new ArrayList<String>();
            for (String arm : taken) {
                if (!own.contains(arm) && Refutations.ordinal(arm).equals(
                        Refutations.ordinal(selector))) {
                    repaired.add(arm);
                }
            }
            if (disjunct == null) return repaired;
            Map<String, List<String>> world = worldArms.get(selector);
            for (Map.Entry<String, ReadRow> pairing
                    : takenPairings(disjunct).entrySet()) {
                if (world != null && world.containsKey(SmtLowering
                        .locationKey(pairing.getValue().location()))) {
                    continue;
                }
                repaired.add(Obligation.PAIRING + pairing.getKey() + "="
                        + corpus.world(disjunct.path().sessionId).pairings
                        .get(pairing.getKey()));
            }
            return repaired;
        }

        public List<String> worldRun(Disjunct selected) {
            List<String> held = ownRun(selected.selector());
            Map<String, List<String>> world =
                    worldArms.get(selected.selector());
            if (world != null) {
                for (List<String> plants : world.values()) {
                    held.remove("(assert (not " + VmTermLowering.or(plants)
                            + "))");
                }
            }
            held.addAll(worldPlants(selected));
            return held;
        }

        public List<String> worldPlants(Disjunct selected) {
            List<String> held = new ArrayList<String>();
            Map<String, List<String>> world =
                    worldArms.get(selected.selector());
            if (world == null) return held;
            for (List<String> arms : world.values()) {
                held.add("(assert " + VmTermLowering.or(arms) + ")");
            }
            return held;
        }

        public Map<String, ReadRow> takenPairings(Disjunct selected) {
            Map<String, ReadRow> taken = new LinkedHashMap<String, ReadRow>();
            String session = selected.path().sessionId;
            for (Map.Entry<String, ReadRow> realized
                    : realizedPairings(selected).entrySet()) {
                if (anotherWriter(corpus, session, Collections
                        .singletonList(realized.getValue()))) {
                    taken.put(realized.getKey(), realized.getValue());
                }
            }
            return taken;
        }

        public Map<String, ReadRow> realizedPairings(Disjunct selected) {
            Map<String, ReadRow> realized =
                    new LinkedHashMap<String, ReadRow>();
            String session = selected.path().sessionId;
            Map<String, String> pairings = corpus.world(session).pairings;
            SessionReader rows = corpus.session(session);
            if (pairings.isEmpty() || rows == null) return realized;
            for (ReadRow read : rows.reads()) {
                String reader = Confirmation.id(read.endpoint());
                String writer = pairings.get(reader);
                if (writer == null || realized.containsKey(reader)) continue;
                WriteRow write = corpus.writeOf(session, SmtLowering
                        .locationKey(read.location()), read.observedVersion());
                if (write != null
                        && writer.equals(Confirmation.writer(write))) {
                    realized.put(reader, read);
                }
            }
            return realized;
        }

        public List<String> observedArrivals(String pathId) {
            return asserted(observedArrivals.get(pathId));
        }

        public List<String> recordedPairings() {
            List<String> held = new ArrayList<String>();
            for (Disjunct disjunct : disjuncts) {
                String pairing = recordedPairing(disjunct);
                if (pairing != null) held.add(pairing);
            }
            return held;
        }

        public String recordedPairing(String selector) {
            for (Disjunct disjunct : disjuncts) {
                if (disjunct.selector().equals(selector)) {
                    return recordedPairing(disjunct);
                }
            }
            return null;
        }

        private String recordedPairing(Disjunct disjunct) {
            List<String> terms = new ArrayList<String>();
            List<String> reads = observedReads.get(disjunct.path().pathId);
            List<String> arrivals = heldArrivals.get(disjunct.path().pathId);
            if (reads != null) terms.addAll(reads);
            if (arrivals != null) terms.addAll(arrivals);
            if (terms.isEmpty()) return null;
            return "(assert (=> " + disjunct.selector() + " "
                    + VmTermLowering.and(terms) + "))";
        }

        private static List<String> asserted(List<String> terms) {
            List<String> asserted = new ArrayList<String>();
            if (terms == null) return asserted;
            for (String term : terms) asserted.add("(assert " + term + ")");
            return asserted;
        }

        public String seedSessionId() {
            return seedSessionId;
        }

        public boolean ranModel(Disjunct selected,
                                Map<String, String> movedRoots) {
            return ran(selected, movedRoots, true);
        }

        public boolean ranRoots(Disjunct selected,
                                Map<String, String> movedRoots) {
            return ran(selected, movedRoots, false);
        }

        public boolean ranWorld(Disjunct selected,
                                Map<String, String> movedRoots,
                                Set<String> readers) {
            String session = selected.path().sessionId;
            SessionReader rows = corpus.session(session);
            SessionReader seed = corpus.session(seedSessionId);
            if (rows == null || seed == null) return false;
            return Moved.of(movedRoots, clockRootReadings, rows, seed)
                    .ranWorldBy(corpus.world(session), rows, readers);
        }

        public enum FatalPath {
            CONE,
            ANCHOR,
            WROTE
        }

        public FatalPath onFatalPath(Disjunct selected, ReadRow read) {
            Set<String> cone = cone(selected.selector());
            if (named(cone, read.symbol())) return FatalPath.CONE;
            OccurrenceAddress reader = read.endpoint().occurrence();
            if (reader.equals(selected.path().occurrence)) {
                return FatalPath.ANCHOR;
            }
            String session = selected.path().sessionId;
            SessionReader rows = corpus.session(session);
            if (rows == null) return null;
            Map<String, List<ReadRow>> observed = readsByVersion(session);
            OccurrenceAddress anchorOccurrence = selected.path().occurrence;
            Map<OccurrenceAddress, Boolean> its =
                    new HashMap<OccurrenceAddress, Boolean>();
            its.put(reader, Boolean.TRUE);
            for (WriteRow write : rows.writes()) {
                OccurrenceAddress writer = write.endpoint().occurrence();
                if (write.initial() || !its.computeIfAbsent(writer,
                        occurrence -> reader.role() && corpus.rolePrefix(
                                session, read, occurrence))) {
                    continue;
                }
                for (ReadRow seen : observed.getOrDefault(
                        write.location() + "@" + write.version(),
                        Collections.<ReadRow>emptyList())) {
                    if (named(cone, seen.symbol()) || anchorOccurrence
                            .equals(seen.endpoint().occurrence())) {
                        return FatalPath.WROTE;
                    }
                }
            }
            return null;
        }

        private final Map<String, Map<String, List<ReadRow>>> readsByVersion =
                new HashMap<String, Map<String, List<ReadRow>>>();

        private synchronized Map<String, List<ReadRow>> readsByVersion(
                String session) {
            return readsByVersion.computeIfAbsent(session, id -> {
                Map<String, List<ReadRow>> index =
                        new HashMap<String, List<ReadRow>>();
                for (ReadRow read : corpus.session(id).reads()) {
                    index.computeIfAbsent(read.location() + "@"
                                    + read.observedVersion(),
                            key -> new ArrayList<ReadRow>()).add(read);
                }
                return index;
            });
        }

        private static boolean named(Set<String> cone, String symbol) {
            return symbol != null && (cone.contains(symbol)
                    || cone.contains(SmtNames.legalSymbols(symbol)));
        }

        public Valuation worldValuation(int ordinal, Disjunct selected) {
            Map<String, String> planted = corpus.world(
                    selected.path().sessionId).rootAssignments;
            Map<String, String> model = new LinkedHashMap<String, String>();
            for (Map.Entry<String, RootMintRow> root
                    : declaredRoots.entrySet()) {
                String value = planted.get(root.getKey());
                if (value != null) {
                    model.put(SmtNames.legalSymbols(root.getValue()
                            .symbol()), value);
                }
            }
            return modelValuation(ordinal, model);
        }

        public List<String> worldClocks(Disjunct selected) {
            Map<String, String> deltas = corpus.world(
                    selected.path().sessionId).clockDeltas;
            Map<String, String> rootOf = new LinkedHashMap<String, String>();
            SessionReader seed = corpus.session(seedSessionId);
            if (seed != null) {
                for (RootMintRow row : seed.roots()) {
                    rootOf.putIfAbsent(row.symbol(), row.rootId());
                }
            }
            List<String> pins = new ArrayList<String>();
            for (String cell : clockCells) {
                String root = rootOf.get(cell);
                String skew = root == null ? null : deltas.get(root);
                String reading = root == null ? null
                        : clockRootReadings.get(root);
                String pin = skew != null && reading != null
                        ? "(= (- " + cell + " " + integralLiteral(reading)
                        + ") " + integralLiteral(skew) + ")"
                        : clockStep(cell, clockReadings, clockBefore, 0);
                pins.add("(assert (! " + pin + " :named world_clock__"
                        + ArtifactIO.digest(cell, 10) + "))");
            }
            return pins;
        }

        private boolean ran(Disjunct selected, Map<String, String> movedRoots,
                            boolean clocks) {
            String session = selected.path().sessionId;
            SessionReader rows = corpus.session(session);
            SessionReader seed = corpus.session(seedSessionId);
            if (rows == null || seed == null) return false;
            Moved moved = Moved.of(movedRoots, clockRootReadings, rows, seed);
            Corpus.World world = corpus.world(session);
            return clocks ? moved.ranBy(world, rows)
                    : moved.ranRootsBy(world, rows);
        }

        public List<JsonObject> refusedPaths() {
            return refusedPaths;
        }

        public boolean assertsRefutations() {
            return !refutations.isEmpty();
        }

        public List<JsonObject> restsOn(List<String> core) {
            List<JsonObject> rows = new ArrayList<JsonObject>();
            if (core == null) return rows;
            for (String label : new LinkedHashSet<String>(core)) {
                Refutations.Refuted model = refutations.get(label);
                if (model == null) continue;
                JsonObject row = new JsonObject();
                row.addProperty("name", label);
                row.addProperty("pathId", model.pathId);
                JsonObject moved = new JsonObject();
                for (Map.Entry<String, String> each
                        : model.moved.entrySet()) {
                    moved.addProperty(each.getKey(), each.getValue());
                }
                row.add("moved", moved);
                row.addProperty("reason", model.reason);
                rows.add(row);
            }
            return rows;
        }

        public List<String> armSelectors() {
            return new ArrayList<String>(armChoices.keySet());
        }

        public boolean offersArms(String selector) {
            String ordinal = Refutations.ordinal(selector);
            for (String arm : armChoices.keySet()) {
                if (Refutations.ordinal(arm).equals(ordinal)) return true;
            }
            return false;
        }

        public ComposedFamilies.ArmChoice arm(String selector) {
            return armChoices.get(selector);
        }

        public List<String> stateSelectors() {
            Set<String> selectors = new LinkedHashSet<String>();
            for (ComposedFamilies.ArmChoice arm : armChoices.values()) {
                for (SmtLowering.StateChoice state : arm.states()) {
                    selectors.add(state.selector);
                }
            }
            return new ArrayList<String>(selectors);
        }

        public List<String> heldSymbols() {
            Set<String> symbols = new LinkedHashSet<String>();
            for (ComposedFamilies.ArmChoice arm : armChoices.values()) {
                for (ComposedFamilies.BoundLeaf leaf : arm.leaves().values()) {
                    if (leaf.held(anchor.id())) symbols.add(leaf.symbol);
                }
            }
            return new ArrayList<String>(symbols);
        }

        public Set<String> cone(String selector) {
            synchronized (cones) {
                Set<String> known = cones.get(selector);
                if (known != null) return known;
            }
            Set<String> cone = coneOf(selector);
            synchronized (cones) {
                cones.put(selector, cone);
            }
            return cone;
        }

        private final Map<String, Set<String>> cones =
                new HashMap<String, Set<String>>();

        private Set<String> coneOf(String selector) {
            Set<String> cone = new LinkedHashSet<String>();
            List<Set<String>> families = new ArrayList<Set<String>>();
            int start = 0;
            for (int index = 0; index < commandEnds.length; index++) {
                int end = commandEnds[index];
                if (selector.equals(commandGuards[index])) {
                    String command = body.substring(start, end);
                    if (command.contains(":named path_fatal__")) {
                        SmtNames.symbols(command, cone);
                    } else if (command.contains(":named message_family__")) {
                        families.add(SmtNames.symbols(command,
                                new LinkedHashSet<String>()));
                    }
                }
                start = end;
            }
            boolean grew = true;
            while (grew) {
                grew = false;
                for (Set<String> family : families) {
                    if (!Collections.disjoint(family, cone)
                            && !cone.containsAll(family)) {
                        cone.addAll(family);
                        grew = true;
                    }
                }
            }
            return cone;
        }

        public List<String> selectors() {
            return Composer.selectors(disjuncts);
        }

        public Disjunct bySelector(String selector) {
            for (Disjunct disjunct : disjuncts) {
                if (disjunct.selector().equals(selector)) return disjunct;
            }
            return null;
        }
    }

    private final Corpus corpus;
    private final OccurrenceAddress anchor;
    private final StaticScopeMap scope;
    private final int maxValuations;
    private final SmtLowering lowering;
    private final List<GapRow> gaps = new ArrayList<GapRow>();
    private final Map<String, Refused> settledLeaves =
            new LinkedHashMap<String, Refused>();
    private final Map<String, Family> families =
            new LinkedHashMap<String, Family>();
    private final Map<String, RootMintRow> declaredRoots =
            new LinkedHashMap<String, RootMintRow>();
    private final Map<String, RootDomain> roots =
            new LinkedHashMap<String, RootDomain>();
    private final Arms arms;
    private final Map<String, Set<String>> unattestedRoots =
            new LinkedHashMap<String, Set<String>>();
    private final Map<String, List<String>> observedReads =
            new LinkedHashMap<String, List<String>>();
    private final Map<String, List<String>> heldArrivals =
            new LinkedHashMap<String, List<String>>();
    private final Map<String, List<String>> observedArrivals =
            new LinkedHashMap<String, List<String>>();
    private final Map<String, Endpoint> openArrivals =
            new LinkedHashMap<String, Endpoint>();
    private Set<String> openedWires;
    private final Set<String> replacing = new LinkedHashSet<String>();
    private String firstRefusal = "";
    private final List<JsonObject> refusedPaths = new ArrayList<JsonObject>();
    private final Map<String, Long> clockTimeline =
            new LinkedHashMap<String, Long>();
    private final Map<String, String> unplacedClocks =
            new LinkedHashMap<String, String>();
    private final Map<String, Refutations.Refuted> refutationNames =
            new LinkedHashMap<String, Refutations.Refuted>();
    private final Map<String, Concrete> pathConcrete =
            new LinkedHashMap<String, Concrete>();
    private final Map<String, Concrete> concrete =
            new LinkedHashMap<String, Concrete>();
    private final ComposedFamilies composedFamilies;
    final RestsOn restsOn;

    private final Set<String> leftOutPaths;

    static final double HEAP_SHARE = 0.8;
    static final String HEAP_BOUND = "COMPOSE_HEAP_BOUND";
    private final DoubleSupplier heapFull;
    private final int maxPaths;

    private Composer(Corpus corpus, OccurrenceAddress anchor,
                     int maxValuations, StaticScopeMap scope,
                     Set<String> leftOutPaths, DoubleSupplier heapFull,
                     int maxPaths) {
        this.corpus = corpus;
        this.anchor = anchor;
        this.scope = scope;
        this.leftOutPaths = leftOutPaths;
        this.heapFull = heapFull;
        this.maxPaths = maxPaths;
        this.restsOn = new RestsOn(corpus, scope, anchor);
        this.maxValuations = maxValuations <= 0 ? 64 : maxValuations;
        this.lowering = new SmtLowering(corpus.declaredSymbols());
        lowering.clockBases(clockBases());
        this.arms = new Arms(corpus);
        this.composedFamilies = new ComposedFamilies(this, corpus, arms,
                lowering, families, unattestedRoots, replacing, gaps);
        reached("indexed");
    }

    private final long began = System.nanoTime();

    private void reached(String phase) {
        System.err.println("compose: " + phase + " at "
                + TimeUnit.NANOSECONDS.toSeconds(System.nanoTime() - began)
                + " s");
    }

    boolean unopened(String consumerEndpointId) {
        return openedWires != null
                && !openedWires.contains(consumerEndpointId);
    }

    public static Composition compose(Corpus corpus,
                                      OccurrenceAddress anchor,
                                      int maxValuations,
                                      StaticScopeMap scope) {
        return compose(corpus, anchor, maxValuations, scope,
                Collections.<String>emptySet(), 0);
    }

    public static Composition compose(Corpus corpus,
                                      OccurrenceAddress anchor,
                                      int maxValuations,
                                      StaticScopeMap scope,
                                      Set<String> leftOutPaths,
                                      int maxPaths) {
        return compose(corpus, anchor, maxValuations, scope, leftOutPaths,
                HeapWatch::oldGenerationSwept, maxPaths);
    }

    static Composition compose(Corpus corpus, OccurrenceAddress anchor,
                               int maxValuations, StaticScopeMap scope,
                               Set<String> leftOutPaths,
                               DoubleSupplier heapFull, int maxPaths) {
        return new Composer(corpus, anchor, maxValuations, scope,
                leftOutPaths, heapFull, maxPaths).run();
    }

    private static final int PROGRESS_PATHS = 25;

    private Composition run() {
        for (Map.Entry<String, Set<String>> collision
                : corpus.collidingRootSymbols().entrySet()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    collision.getKey(), "one solver name for "
                            + collision.getValue().size() + " roots: "
                            + collision.getValue());
        }

        Set<String> leftOutSessions = new LinkedHashSet<String>();
        for (SessionReader session : corpus.sessions()) {
            if (session.incomplete().isEmpty()) continue;
            leftOutSessions.add(session.sessionId());
            gap(GapKind.SESSION_INCOMPLETE, GapClass.DIAGNOSTIC,
                    session.sessionId(), "this session could not be read "
                            + "whole, so its paths are left out: "
                            + session.incomplete());
        }

        for (SessionReader session : corpus.sessions()) {
            for (ObligationResult settled : session.obligations()) {
                ObligationResult wave = corpus.waveVerdict(
                        session.sessionId(), settled.obligationId());
                if (wave == null || wave.verdict() == settled.verdict()) {
                    continue;
                }
                leftOutSessions.add(session.sessionId());
                gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        settled.obligationId(), "the replay that ran this "
                                + "obligation states " + settled.verdict()
                                + " in session " + session.sessionId()
                                + " and the wave's own file states "
                                + wave.verdict() + ": its paths are left out");
            }
        }

        List<String> seeds = corpus.seedSessionIds();
        if (seeds.size() != 1 && !corpus.sessions().isEmpty()) {
            gap(GapKind.UNSTATED_VALUE, seeds.isEmpty() ? GapClass.BLOCKING
                            : GapClass.DIAGNOSTIC, seeds.toString(),
                    seeds.isEmpty()
                            ? "no session of this corpus states role SEED, "
                            + "so none of them is the recording"
                            : seeds.size() + " sessions of this corpus state "
                            + "role SEED; the first is the recording");
        }

        SlotTable slots;
        try {
            slots = SlotTable.read(corpus.iteration());
        } catch (java.io.IOException | RuntimeException unreadable) {
            slots = null;
            gap(GapKind.TOPOLOGY_DIVERGENCE, GapClass.DIAGNOSTIC,
                    SlotTable.FILE, "this epoch's slot table could not be "
                            + "read, so no session is known to replace a"
                            + " slot: " + unreadable);
        }
        if (slots != null) {
            for (SlotTable.Replacement replacement
                    : slots.replacements(corpus)) {
                replacing.add(replacement.sessionId);
                gaps.add(GapRow.of(replacement.sessionId,
                        GapKind.TOPOLOGY_DIVERGENCE, GapClass.DIAGNOSTIC,
                        replacement.consumerEndpointId,
                        replacement.detail()));
            }
            if (slots.stated()) openedWires = slots.wireConsumers();
        }

        placeClocks();
        List<Disjunct> disjuncts = new ArrayList<Disjunct>();
        List<PathEntry> entries = new ArrayList<PathEntry>();
        List<Corpus.RecordedPath> admitted = restsOn.admitted(gaps);
        reached(admitted.size() + " path(s) admitted");
        int ordinal = 0;
        int done = 0;
        int bounded = 0;
        long started = System.nanoTime();
        long said = started;
        for (Corpus.RecordedPath path : admitted) {
            boolean defective = leftOutSessions.contains(path.sessionId);
            boolean capped = maxPaths > 0 && ordinal >= maxPaths;
            if (bounded > 0 || capped || ordinal > 0
                    && heapFull.getAsDouble() >= HEAP_SHARE) {
                bounded++;
                refused(path, Collections.singletonList(GapRow.of(
                        path.sessionId, GapKind.ADMISSION_GAP,
                        GapClass.DIAGNOSTIC, HEAP_BOUND, "left out (best "
                                + "effort): " + (capped ? "at most " + maxPaths
                                + " paths are composed (--max-paths: the "
                                + "case's compose_max_paths, or a composition "
                                + "of more ran out of the engine heap)"
                                : "the composer's old "
                                + "generation was past "
                                + Math.round(HEAP_SHARE * 100) + " % after "
                                + "its last sweep with " + ordinal
                                + " path(s) composed") + ", and the claim says "
                                + "nothing of " + path.pathId)));
            } else if (defective || leftOutPaths.contains(path.pathId)) {
                refused(path, Collections.singletonList(GapRow.of(
                        path.sessionId, GapKind.ADMISSION_GAP,
                        GapClass.DIAGNOSTIC, path.pathId, "left out (best"
                                + " effort): " + (defective ? "its session is"
                                + " defective" : "z3 refused a query over"
                                + " it"))));
            }
            Disjunct disjunct = bounded > 0 || defective
                    || leftOutPaths.contains(path.pathId) ? null
                    : compose(path, ordinal);
            if (disjunct != null) {
                disjuncts.add(disjunct);
                entries.add(PathEntry.of(path.pathId, path.sessionId,
                        disjunct.selector(), disjunct.fatalObserved(),
                        disjunct.restsOn(), disjunct.cutoff()));
                ordinal++;
            }
            long now = System.nanoTime();
            if (++done % PROGRESS_PATHS == 0 || done == admitted.size()
                    || now - said >= TimeUnit.MINUTES.toNanos(1)) {
                said = now;
                System.err.println("compose: path " + done + " of "
                        + admitted.size() + " (" + ordinal + " composed) in "
                        + TimeUnit.NANOSECONDS.toSeconds(now - started)
                        + " s, the old generation "
                        + Math.round(heapFull.getAsDouble() * 100)
                        + " % after its last sweep");
            }
        }
        if (bounded > 0) {
            System.err.println("compose: " + bounded + " path(s) left out "
                    + "past the heap bound (" + HEAP_BOUND + ")");
        }
        if (disjuncts.isEmpty()) {
            gap(GapKind.ADMISSION_GAP, GapClass.BLOCKING, anchor.render(),
                    admitted.isEmpty()
                            ? "the declared occurrence ran, and no admitted "
                            + "session published a path at it"
                            : admitted.size() + " paths ran the declared "
                            + "occurrence and all were refused: "
                            + (firstRefusal.isEmpty() ? "no refusal was named"
                            : firstRefusal));
        } else {
            List<String> selectors = selectors(disjuncts);
            lowering.assertNamed("target_path_partition",
                    Arms.exactlyOne(selectors));
            lowering.assertNamed("fatal_target",
                    VmTermLowering.or(selectors));
        }

        composedFamilies.outsideTheClosure(disjuncts);

        List<String> clockCells = new ArrayList<String>();
        Map<String, Long> clockReadings = new LinkedHashMap<String, Long>();
        Map<String, Long> clockNanos = new LinkedHashMap<String, Long>();
        Map<String, String> clockBefore = new LinkedHashMap<String, String>();
        clocks(clockCells, clockReadings, clockNanos, clockBefore);
        domains();
        refutations(disjuncts, clockCells, clockReadings, clockBefore);
        reached("clocks, domains and refutations asserted");
        lowering.assertIdentitiesDistinct();
        for (Map.Entry<String, String> conflict
                : lowering.sortConflicts().entrySet()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    conflict.getKey(), "this corpus states one solver name "
                            + "at two sorts: " + conflict.getValue());
        }
        for (Map.Entry<String, String> collision
                : lowering.nameCollisions().entrySet()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    collision.getKey(), "one solver name for two "
                            + "identities of this corpus: "
                            + collision.getValue());
        }
        for (Map.Entry<String, String> cut : lowering.cuts().entrySet()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, cut.getKey(),
                    cut.getValue().isEmpty()
                            ? "the propagation did not carry this value"
                            : cut.getValue());
        }
        for (Map.Entry<String, String> pinned
                : lowering.pinnedReturns().entrySet()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    "MethodReturnPinned:" + pinned.getKey(), "the call that "
                            + "returned this symbol is no relation the "
                            + "lowering knows and nothing its arguments rest "
                            + "on moves: it is pinned to " + pinned.getValue()
                            + " by a named assertion, and what it was "
                            + "computed from is not in the formula");
        }
        for (Map.Entry<String, String> named
                : lowering.diagnostics().entrySet()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    named.getKey(), named.getValue());
        }
        Map<String, Set<String>> settled =
                new LinkedHashMap<String, Set<String>>();
        Map<String, Refused> settledBy = new LinkedHashMap<String, Refused>();
        for (Concrete row : concrete.values()) {
            Refused refused = settledLeaves.get(row.subject);
            if (refused == null || !SmtLowering.settled(row.kind)) continue;
            String key = refused.producer + "\n" + refused.rule + "\n"
                    + row.kind;
            settled.computeIfAbsent(key, k -> new LinkedHashSet<String>())
                    .add(row.subject);
            settledBy.put(key, refused);
        }
        for (Map.Entry<String, Set<String>> leaves : settled.entrySet()) {
            Refused refused = settledBy.get(leaves.getKey());
            String kind = leaves.getKey().substring(
                    leaves.getKey().lastIndexOf('\n') + 1);
            String count = leaves.getValue().size() + " store content leaf(s)"
                    + " this producer wrote ";
            if (SmtLowering.Unbound.BOUNDED.equals(kind)) {
                gap(GapKind.BOUND_INSUFFICIENT, GapClass.DIAGNOSTIC,
                        refused.producer + " " + DAEMON_TICK_BOUND + "="
                                + refused.bound, count + "are held at their"
                                + " versions' values past the bound (boundedBy"
                                + "Tick): " + refused.why);
            } else {
                gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        refused.producer, count + (SmtLowering.Unbound
                                .EXPORTED.equals(kind) ? "are bound by its"
                                + " export without its path condition"
                                + " (exportedByRefusedProducer)"
                                : "are constants of their versions"
                                + " (constantByRefusedProducer)") + ", since"
                                + " no session attests it at their ports: "
                                + refused.why);
            }
        }

        List<Valuation> valuations = valuations();
        reached(valuations.size() + " valuation(s) chosen");
        List<String> pins = new ArrayList<String>();
        for (Valuation valuation : valuations) {
            pins.addAll(valuation.assertions());
        }
        corpus.letGo();
        String body = lowering.body(pins);
        reached("body lowered");
        return new Composition(this, body, disjuncts, entries, valuations,
                clockCells, clockReadings, clockNanos, clockBefore);
    }



    private Disjunct compose(Corpus.RecordedPath path, int ordinal) {
        String session = path.sessionId;
        TargetRow target = corpus.target(session, anchor);
        if (target == null) return null;
        String selector = "path_selector__" + ordinal + "__"
                + ArtifactIO.digest(path.pathId, 10);
        lowering.declare(selector, Sort.BOOL);
        lowering.path();
        RestsOn.Decided decided = restsOn.decided(session, target,
                path.decisions);
        DecisionRow way = decided.way;
        boolean symbolicWay = decided.symbolicWay;
        long cutoff = decided.cutoff;
        String fatalTerm = decided.fatalTerm;
        pathEnd = new PathEnd(session, path.decisions, cutoff);
        RestsOn.Reached reached = restsOn.closure(session, anchor, cutoff,
                null);
        Repairing repairing = repairing(session, reached, cutoff,
                target.reachedAnchor() ? corpus.readEvents(session,
                        target.phiTerm()) : Collections.<Long>emptySet());
        Set<String> pinned = repairing.pinned;
        Set<String> moved = repairing.keys;
        SmtLowering.SessionJoin rows = SmtLowering.repairing(
                corpus.join(session),
                (location, event) -> moved.contains(
                        SmtLowering.readKey(location, event)),
                (reader, writer) -> arms.concurrent(reader, writer, session));
        lowering.begin(session, rows, corpus.expressions(session));

        List<String> terms = new ArrayList<String>();
        List<GapRow> refusals = new ArrayList<GapRow>();
        List<ReadRow> joined = new ArrayList<ReadRow>();
        List<String> observed = new ArrayList<String>();
        Map<String, String> joins = new LinkedHashMap<String, String>();
        pathConcrete.clear();
        int unboundBefore = lowering.unbound().size();
        frames(session, reached.keySet());

        List<DecisionRow> conditions = RestsOn.before(path.decisions, cutoff);
        conditions.addAll(restsOn.reachedConditions(session, reached));
        Independence relevant = restsOn.independence(session,
                Collections.singletonList(fatalTerm),
                familyBound(session, repairing.reads), reached,
                conditions);
        Set<String> fatalLocations = new LinkedHashSet<String>(
                restsOn.independence(session, fatalRests(fatalTerm,
                        path.decisions, cutoff),
                        Collections.<String>emptySet(), reached, conditions)
                        .locations());
        fatalLocations.addAll(restsOn.storeLocations(session, reached));

        Set<String> answered = new LinkedHashSet<String>();
        statedReads(session, reached.keySet(), relevant, rows, refusals,
                joins, answered);

        Map<String, Set<String>> unminted =
                new LinkedHashMap<String, Set<String>>();
        terms.addAll(valuationOf(session, refusals, unminted));

        Set<String> handoffs = new LinkedHashSet<String>();
        List<String> holds = new ArrayList<String>();
        List<AttachRow> bound = new ArrayList<AttachRow>();
        handoffReads(session, handoffs, holds, bound);

        stateJoins(session, reached.keySet(), relevant, rows, refusals,
                joined, joins, answered);
        joined.removeIf(read -> pinned.contains(
                SmtLowering.locationKey(read.location())));
        for (ReadRow read : joined) {
            if (moved.contains(SmtLowering.readKey(SmtLowering.locationKey(
                    read.location()), read.seq()))) {
                lowering.movable(read);
            }
        }

        terms.addAll(prefix(path.decisions, cutoff, "decision ",
                relevant, refusals));

        terms.addAll(closureConditions(session, reached, relevant,
                refusals));

        String subject = "phi of " + anchor.render();
        String published = target.phiTerm().trim();
        int fatalArm = -1;
        if (!target.reachedAnchor()) {
            pathConcrete.put("way:" + session, way != null
                    ? new Concrete("WAY", way.siteId() + "#" + way.ordinal(),
                    way.outcome() + (way.term().isEmpty() ? ""
                            : " " + way.term()), "the guard the path left the"
                    + " way to the throw at", new ArrayList<String>(
                    corpus.termSymbols(session, way.term())))
                    : new Concrete("WAY", anchor.render(), "",
                    decided.cut.isEmpty() && decided.defect.isEmpty()
                            ? "the path stopped on the way to the throw: it"
                            + " left it at no guard"
                            : "the path stopped on the way to the throw: a"
                            + " loop bound cut its occurrence ("
                            + (decided.cut.isEmpty() ? decided.defect
                            : decided.cut) + ")",
                    Collections.<String>emptyList()));
            List<GapRow> named = new ArrayList<GapRow>();
            restsOn.cut(named, session, decided);
            gaps.addAll(named);
            String fatal = symbolicWay ? lowering.statedTerm(fatalTerm,
                    "way:" + subject) : fatalTerm;
            if (!fatal.isEmpty() && !unknown(fatal, refusals, subject)) {
                fatalArm = terms.size();
                terms.add(fatal);
            }
            terms.addAll(healthyDecisions(session, ordinal, path.decisions,
                    symbolicWay ? cutoff - 1 : cutoff, relevant));
        } else if (published.isEmpty()) {
            refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, subject, "the target row states "
                            + "no phi (invariant 9), so what the fatal rests "
                            + "on is stated by no row"));
        } else if ("false".equals(published)) {
            fatalArm = terms.size();
            terms.add(published);
            terms.addAll(healthyDecisions(session, ordinal, path.decisions,
                    target.seq(), relevant));
        } else {
            String phi = lowering.statedTerm(published, "phi:" + subject);
            if (!phi.isEmpty() && !unknown(phi, refusals, subject)) {
                fatalArm = terms.size();
                terms.add(phi);
            }
        }

        List<String> reaching = new ArrayList<String>(terms);
        reaching.addAll(joins.values());
        reaching.addAll(holds);
        reachedHandoffs(session, lowering.reachedSymbols(reaching), handoffs,
                holds, bound, refusals, "");
        terms.addAll(holds);
        Map<String, List<AttachRow>> viewVersions =
                new LinkedHashMap<String, List<AttachRow>>();
        Map<String, Set<String>> guarded = lowering.viewGuarded();
        for (Iterator<AttachRow> each = bound.iterator(); each.hasNext();) {
            AttachRow attach = each.next();
            Set<String> choices = guarded.get(attach.symbol());
            if (choices == null) continue;
            each.remove();
            for (String choice : choices) {
                viewVersions.computeIfAbsent(choice,
                        unused -> new ArrayList<AttachRow>()).add(attach);
            }
        }
        Set<String> interactionIds = new LinkedHashSet<String>();
        for (AttachRow attach : bound) {
            interactionIds.add(attach.interaction().id());
        }

        List<String> refused = new ArrayList<String>(
                lowering.openRefusals());
        terms.addAll(lowering.end());

        if (!unminted.isEmpty() || !unplacedClocks.isEmpty()) {
            Set<String> named = named(terms, joins);
            unstatedRoots(session, unminted, named, refusals);
            unplacedClocks(session, named, refusals);
        }
        for (String refusal : refused) {
            gaps.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, refusal,
                    "this path rests on a value the lowering has no semantics"
                            + " for: the value is free, over-approximated"));
        }
        if (!refusals.isEmpty()) {
            refused(path, refusals);
            return null;
        }

        List<String> familyTerms = new ArrayList<String>();
        List<GapRow> unproducible = new ArrayList<GapRow>();
        if (!composedFamilies.closeFamilies(ordinal, selector, session,
                interactionIds, bound, familyTerms, unproducible)) {
            composedFamilies.discard();
            refused(path, unproducible);
            return null;
        }
        Map<String, String> unpaired = unattestedVersions(session, guarded,
                viewVersions, unboundBefore);
        for (String version : unpaired.keySet()) {
            viewVersions.remove(version);
        }
        for (String version : composedFamilies.closeViewVersions(ordinal,
                viewVersions, interactionIds, familyTerms)) {
            unpaired.put(version, "no session of this corpus can send what"
                    + " the view holds at this version");
        }
        for (Map.Entry<String, String> version : unpaired.entrySet()) {
            terms.add("(not " + version.getKey() + ")");
            for (Map.Entry<String, Set<String>> leaf : guarded.entrySet()) {
                if (leaf.getValue().contains(version.getKey())) {
                    lowering.unpaired(leaf.getKey(), version.getValue()
                            + " (" + lowering.viewGuardName(version.getKey())
                            + "): the read is not paired to it");
                }
            }
        }
        Set<String> chosen = composedFamilies.stateFamilies(path,
                ordinal, selector, joined, joins, interactionIds,
                familyTerms, observed, repairing.planted);
        terms.addAll(statedJoins(joins, chosen, terms, familyTerms));

        composedFamilies.commit();
        String fatal = "path_fatal__" + ordinal;
        List<String> withoutFatalArm = new ArrayList<String>(terms);
        if (fatalArm >= 0) withoutFatalArm.remove(fatalArm);
        String conjunction = fatalArm >= 0
                && "false".equals(terms.get(fatalArm))
                ? "(and " + VmTermLowering.and(withoutFatalArm) + " false)"
                : VmTermLowering.and(terms);
        lowering.assertNamed(fatal,
                "(=> " + selector + " " + conjunction + ")");
        observedReads.put(path.pathId, observed);
        for (SmtLowering.Unbound value : lowering.unbound().subList(
                unboundBefore, lowering.unbound().size())) {
            Concrete row = new Concrete(value.kind, value.subject,
                    value.value, value.reason, value.movesWith)
                    .in(value.arm);
            if (SmtLowering.Unbound.UNPAIRED.equals(value.kind)) {
                pathConcrete.put(value.subject + "|" + value.arm, row);
            } else {
                pathConcrete.putIfAbsent(value.subject + "|" + value.arm,
                        row);
            }
        }
        for (Map.Entry<String, Concrete> row : pathConcrete.entrySet()) {
            concrete.put(path.pathId + "|" + row.getKey(),
                    row.getValue().on(path.pathId));
        }
        observedArrivals.put(path.pathId,
                arrivals(corpus.attachesOn(session, anchor)));
        heldArrivals.put(path.pathId, arrivals(bound));
        return new Disjunct(path, selector, fatal, "(=> " + selector + " "
                + VmTermLowering.and(withoutFatalArm) + ")",
                target.observedFatal(), interactionIds, fatalLocations, cutoff);
    }

    private Map<String, String> unattestedVersions(
            String session, Map<String, Set<String>> guarded,
            Map<String, List<AttachRow>> viewVersions, int unboundBefore) {
        Set<String> sent = new HashSet<String>();
        for (List<AttachRow> attaches : viewVersions.values()) {
            for (AttachRow attach : attaches) sent.add(attach.symbol());
        }
        Set<String> settled = new HashSet<String>();
        for (SmtLowering.Unbound value : lowering.unbound().subList(
                unboundBefore, lowering.unbound().size())) {
            if (SmtLowering.settled(value.kind)) settled.add(value.subject);
        }
        Map<String, String> unpaired = new LinkedHashMap<String, String>();
        for (Map.Entry<String, Set<String>> leaf : guarded.entrySet()) {
            String symbol = leaf.getKey();
            if (!symbol.contains(Cone.BOUNDARY) || sent.contains(symbol)
                    || settled.contains(symbol)
                    || corpus.attach(session, symbol) == null) {
                continue;
            }
            for (String version : leaf.getValue()) {
                unpaired.putIfAbsent(version, "its leaf " + symbol + " has"
                        + " no sender the corpus attests");
            }
        }
        for (Map.Entry<String, String> version : unpaired.entrySet()) {
            gap(GapKind.UNPRODUCIBLE_ANSWER, GapClass.DIAGNOSTIC,
                    lowering.viewGuardName(version.getKey()),
                    version.getValue() + ", so the read is not paired to"
                            + " this version: the path holds its version"
                            + " choice false");
        }
        return unpaired;
    }

    private static List<String> fatalRests(String fatalTerm,
                                           List<DecisionRow> decisions,
                                           long cutoff) {
        String phi = fatalTerm.trim();
        return "true".equals(phi) || "false".equals(phi)
                ? Arms.pathCondition(decisions, cutoff)
                : Collections.singletonList(fatalTerm);
    }

    private List<String> healthyDecisions(String session, int ordinal,
                                          List<DecisionRow> decisions,
                                          long upTo,
                                          Independence relevant) {
        List<String> stated = new ArrayList<String>();
        for (DecisionRow decision : decisions) {
            if (decision.seq() > upTo || relevant.keeps(decision)
                    && decision.seq() < upTo
                    && Arms.predicate(Arms.conjunct(decision))) {
                continue;
            }
            String subject = decision.siteId() + "#" + decision.ordinal();
            String name = "decided__" + ordinal + "__" + ArtifactIO.digest(
                    session + "|" + subject, 12);
            lowering.declare(name, Sort.BOOL);
            stated.add(decision.outcome() ? name : "(not " + name + ")");
            pathConcrete.put("decision:" + session + ":" + subject,
                    new Concrete("DECISION", subject, decision.outcome()
                            + (decision.term().isEmpty() ? ""
                            : " " + decision.term()), "a decision over "
                            + "nothing that moves, stated as a proposition",
                            Collections.singletonList(name)));
        }
        return stated;
    }

    private static List<String> selectors(List<Disjunct> disjuncts) {
        List<String> selectors = new ArrayList<String>();
        for (Disjunct disjunct : disjuncts) selectors.add(disjunct.selector());
        return selectors;
    }

    private void refused(Corpus.RecordedPath path, List<GapRow> rows) {
        gaps.addAll(rows);
        if (rows.isEmpty()) return;
        GapRow first = rows.get(0);
        String reason = first.kind() + " " + first.subject() + ": "
                + first.detail();
        if (firstRefusal.isEmpty()) firstRefusal = reason;
        JsonObject row = new JsonObject();
        row.addProperty("pathId", path.pathId);
        row.addProperty("sessionId", path.sessionId);
        row.addProperty("refusals", rows.size());
        row.addProperty("reason", reason);
        refusedPaths.add(row);
    }

    List<String> statedJoins(Map<String, String> joins,
                                     Set<String> chosen, List<String> terms,
                                     List<String> familyTerms) {
        Map<String, String> pending = new LinkedHashMap<String, String>();
        for (Map.Entry<String, String> join : joins.entrySet()) {
            if (chosen.contains(join.getKey())) continue;
            pending.put(join.getKey(), join.getValue());
        }
        Set<String> asked = new LinkedHashSet<String>();
        List<String> reaching = new ArrayList<String>(terms);
        reaching.addAll(familyTerms);
        while (!reaching.isEmpty()) {
            Set<String> reached = lowering.reachedSymbols(reaching);
            reaching = new ArrayList<String>();
            for (String symbol : reached) {
                String join = pending.remove(symbol);
                if (join == null) continue;
                asked.add(symbol);
                reaching.add(join);
            }
        }
        List<String> stated = new ArrayList<String>();
        for (Map.Entry<String, String> join : joins.entrySet()) {
            if (asked.contains(join.getKey())) stated.add(join.getValue());
        }
        return stated;
    }

    private List<String> valuationOf(String session,
                                     List<GapRow> refusals,
                                     Map<String, Set<String>> unminted) {
        List<String> valuation = new ArrayList<String>();
        for (Map.Entry<String, List<RootMintRow>> entry
                : corpus.roots().entrySet()) {
            RootMintRow any = corpus.anyRoot(entry.getKey());
            RootMintRow row = corpus.root(entry.getKey(), session);
            if (any == null || any.kind() == RootKind.CLOCK) continue;
            RootMintRow concrete = row == null
                    ? corpus.ranRoot(entry.getKey(), session) : null;
            if (concrete != null) {
                String literal = smtLiteral(corpus.rootValue(session,
                        concrete.rootId()), sortOf(concrete));
                if (literal.isEmpty()) continue;
                lowering.declareStated(concrete.symbol(), sortOf(concrete));
                valuation.add("(= " + concrete.symbol() + " " + literal
                        + ")");
                continue;
            }
            if (row == null) {
                if (any.declared()) {
                    Set<String> symbols = new LinkedHashSet<String>();
                    for (RootMintRow mint : entry.getValue()) {
                        if (mint != null && !mint.symbol().isEmpty()) {
                            symbols.add(mint.symbol());
                        }
                    }
                    if (!symbols.isEmpty()) {
                        unminted.put(any.rootId(), symbols);
                    }
                }
                continue;
            }
            String ran = corpus.rootValue(session, row.rootId());
            if (ran.isEmpty() && row.declared()) {
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.DIAGNOSTIC, any.rootId(),
                        "this replay minted a declared root and states no "
                                + "value it ran it at: its mint states none "
                                + "and no obligation it ran under assigns "
                                + "it"));
                continue;
            }
            String read = corpus.rootReading(session, row.rootId());
            if (!read.isEmpty() && !read.equals(ran)) {
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.DIAGNOSTIC, any.rootId(),
                        "this session's mint states \"" + read + "\" and the "
                                + "obligation it ran under assigns \"" + ran
                                + "\", so what this replay ran the root at "
                                + "is stated twice and differently"));
                continue;
            }
            if (!corpus.varied(row.rootId())) continue;
            lowering.declareStated(row.symbol(), sortOf(row));
            String window = windowOf(row);
            if (!window.isEmpty()) {
                valuation.add(window);
                continue;
            }
            String literal = smtLiteral(ran, sortOf(row));
            if (literal.isEmpty()) continue;
            valuation.add("(= " + row.symbol() + " " + literal + ")");
        }
        return valuation;
    }

    private Set<String> named(List<String> terms, Map<String, String> joins) {
        List<String> texts = new ArrayList<String>(terms);
        texts.addAll(joins.values());
        Set<String> named = lowering.reachedSymbols(texts);
        for (String text : texts) named.addAll(SmtNames.names(text));
        return named;
    }

    private void unstatedRoots(String session,
                               Map<String, Set<String>> unminted,
                               Set<String> named,
                               List<GapRow> refusals) {
        for (Map.Entry<String, Set<String>> root : unminted.entrySet()) {
            for (String symbol : root.getValue()) {
                if (!named.contains(symbol)) continue;
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.DIAGNOSTIC, root.getKey(),
                        "this path's own terms name this declared root ("
                                + symbol + ") and this session minted no "
                                + "value for it, so what the path rests on "
                                + "is stated by no row of the execution it "
                                + "is about"));
                break;
            }
        }
    }

    private void unplacedClocks(String session, Set<String> named,
                                List<GapRow> refusals) {
        for (Map.Entry<String, String> cell : unplacedClocks.entrySet()) {
            if (!named.contains(cell.getKey())) continue;
            refusals.add(GapRow.of(session, GapKind.DECLARATION_MISSING,
                    GapClass.DIAGNOSTIC, cell.getValue(), "this path rests "
                            + "on clock cell " + cell.getKey() + ", which the "
                            + "recording never read, and no session that "
                            + "read it read a cell of the same clock the "
                            + "recording read, so it has no instant on the "
                            + "recording's timeline: no claim could say "
                            + "whether a witness moved it, and the path is "
                            + "not in the disjunction"));
        }
    }

    private String windowOf(RootMintRow row) {
        if (!row.declared() || row.kind() == RootKind.MARKER) return "";
        RootDomain domain = domainOf(row);
        String min = domain.min();
        String max = domain.max();
        if (min == null || max == null || integralLiteral(min).isEmpty()
                || integralLiteral(max).isEmpty()) {
            return "";
        }
        return window(row.symbol(), min, max);
    }

    private static String window(String symbol, String min, String max) {
        return "(and (>= " + symbol + " " + integralLiteral(min) + ") (<= "
                + symbol + " " + integralLiteral(max) + "))";
    }

    private void handoffReads(String session, Set<String> handoffs,
                              List<String> holds, List<AttachRow> bound) {
        for (AttachRow attach : corpus.attachesOn(session, anchor)) {
            if (handoffs.add(attach.symbol())) {
                arrival(session, attach, holds, bound);
            }
        }
    }

    void reachedHandoffs(String session, Collection<String> names,
                         Set<String> handoffs, List<String> holds,
                         List<AttachRow> bound, List<GapRow> refusals,
                         String arm) {
        List<String> pending = new ArrayList<String>(names);
        for (int at = 0; at < pending.size(); at++) {
            String name = pending.get(at);
            if (handoffs.contains(name)) continue;
            AttachRow attach = corpus.attach(session, name);
            if (attach != null) {
                handoffs.add(name);
                int held = holds.size();
                arrival(session, attach, holds, bound);
                pending.addAll(lowering.reachedSymbols(
                        holds.subList(held, holds.size())));
            } else if (corpus.handoffSymbol(name) && handoffs.add(name)) {
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.DIAGNOSTIC, name, (arm.isEmpty()
                                ? "this path" : "arm " + arm) + " names a "
                                + "handoff variable no attach row of its "
                                + "session minted, so no family of this "
                                + "run binds what it read"));
            }
        }
    }

    private void arrival(String session, AttachRow attach,
                         List<String> holds, List<AttachRow> bound) {
        if (attach.interaction() == null) {
            composedFamilies.unpaired(session, attach);
        }
        List<ExportRow> attested = new ArrayList<ExportRow>();
        if (attach.producer() != null) {
            for (ExportRow export : arms.attestedDeliveries(
                    attach.interaction(), session)) {
                if (!replacing.contains(export.sessionId())) {
                    attested.add(export);
                }
            }
        }
        if (attestedArrival(attach, attested)) {
            bound.add(attach);
            return;
        }
        Sort sort = JavaSmtSorts.sortOfJava(attach.javaType());
        openArrivals.put(SmtNames.legalSymbols(attach.symbol()),
                attach.producer());
        if (!attested.isEmpty()) {
            lowering.declareStated(attach.symbol(), sort);
            lowering.freedArrival(attach.symbol(), attested.size()
                    + " attested delivery(ies) of producer "
                    + attach.producer().id() + " (a run that paired it with"
                    + " this consumer ran it instrumented) did not lower to"
                    + " a value of the read's sort");
            return;
        }
        String received = JsonFields.firstNonBlank(attach.answeredValue(),
                attach.arrival());
        Refused refused = refusedByRule(attach);
        Delivery delivery = refused == null ? null : delivery(attach);
        if (delivery != null && !delivery.constant) {
            lowering.declareStated(attach.symbol(), sort);
            holds.add(delivery.binding);
            lowering.settledByRefusedProducer(SmtLowering.Unbound.EXPORTED,
                    attach.symbol(), received, refused.why);
            settledLeaves.put(attach.symbol(), refused);
            return;
        }
        Term value = arrived(attach);
        if (value == null) {
            lowering.declareStated(attach.symbol(), sort);
            lowering.freedArrival(attach.symbol(), "no producer is attested "
                    + "and its row states the value \"" + received
                    + "\", which this lowering places nowhere");
            return;
        }
        lowering.declareStated(attach.symbol(), value.sort);
        holds.add("(= " + attach.symbol() + " " + value.text + ")");
        if (delivery != null) {
            lowering.settledByRefusedProducer(refused.bound < 0
                    ? SmtLowering.Unbound.CONSTANT
                    : SmtLowering.Unbound.BOUNDED, attach.symbol(), received,
                    refused.why);
            settledLeaves.put(attach.symbol(), refused);
            return;
        }
        lowering.held(attach.symbol(), received, attach.producer() == null
                ? "the attach names no producer"
                : unattestedWhy(attach.producer()) + (refused == null ? ""
                : ", and its own run's export at the port lowers to"
                + " nothing (" + refused.why + ")"));
    }

    private String unattestedWhy(Endpoint producer) {
        Set<String> instrumented = new LinkedHashSet<String>();
        for (ExportRow export : corpus.exportsOf(producer)) {
            if (arms.attested(export.sessionId(), producer.occurrence())) {
                instrumented.add(export.sessionId());
            }
        }
        return instrumented.isEmpty()
                ? "no session ran its producer " + producer.id()
                + " instrumented"
                : "its producer " + producer.id() + " ran instrumented in "
                + instrumented.size() + " run(s), none of which paired it"
                + " with this consumer";
    }

    private Refused refusedByRule(AttachRow attach) {
        if (attach.producer() == null
                || ContentPort.parse(attach.endpoint().site()) == null) {
            return null;
        }
        OccurrenceAddress producer = attach.producer().occurrence();
        if (producer.role()) {
            return new Refused(producer.render(), "ROLE", producer.regionId()
                    + " is a role, no region a weave captures", -1);
        }
        Corpus.TickPast tick = corpus.tickPastRecording(producer);
        return tick == null ? new Refused(producer.render(), "UNATTESTED",
                "where it wrote this port, "
                        + unattestedWhy(attach.producer()), -1)
                : new Refused(producer.render(), "TICK_BOUND",
                "begun by the daemon tick " + tick, tick.last);
    }

    private static final class Refused {
        final String producer;
        final String rule;
        final String why;
        final int bound;

        Refused(String producer, String rule, String why, int bound) {
            this.producer = producer;
            this.rule = rule;
            this.why = rule + ": " + why;
            this.bound = bound;
        }
    }

    private static final class Delivery {
        final String binding;
        final boolean constant;

        Delivery(String binding, boolean constant) {
            this.binding = binding;
            this.constant = constant;
        }
    }

    private Delivery delivery(AttachRow attach) {
        List<ExportRow> own = new ArrayList<ExportRow>();
        for (ExportRow export : corpus.exportsOf(attach.producer())) {
            if (export.sessionId().equals(attach.sessionId())) own.add(export);
        }
        own.addAll(corpus.ownExportsOf(attach.sessionId(),
                attach.producer()));
        Sort sort = JavaSmtSorts.sortOfJava(attach.javaType());
        List<String> alternatives = new ArrayList<String>();
        boolean constant = true;
        for (ExportRow export : own) {
            List<String> conditions = new ArrayList<String>();
            Term delivered = composedFamilies.lower(export.sessionId(),
                    export.expressionRef(), "refused-producer-export",
                    conditions);
            if (delivered == null) continue;
            String received = lowering.leafEquals(attach.symbol(), sort,
                    attach.javaType(), delivered, export.javaType());
            if (received == null) {
                lowering.leafUnrelated(attach.symbol(), sort, delivered.sort);
                continue;
            }
            SessionReader reader = corpus.session(export.sessionId());
            Set<String> symbols = new LinkedHashSet<String>();
            Arms.symbolsIn(reader.expressions().expression(
                    export.expressionRef()), symbols);
            constant &= symbols.isEmpty();
            conditions.add(received);
            alternatives.add(VmTermLowering.and(conditions));
        }
        return alternatives.isEmpty() ? null : new Delivery(
                VmTermLowering.or(alternatives), constant);
    }

    static String pinnedRoot(String assertion) {
        String opening = "(assert (! (= ";
        if (assertion == null || !assertion.startsWith(opening)
                || !assertion.contains(":named " + VALUATION_PIN)) {
            return null;
        }
        int end = assertion.indexOf(' ', opening.length());
        return end < 0 ? null : assertion.substring(opening.length(), end);
    }

    static final String VALUATION_PIN = "valuation__";

    static Sort sortOf(RootMintRow row) {
        return row.kind() == RootKind.MARKER ? Sort.BOOL : Sort.INT;
    }

    private boolean attestedArrival(AttachRow attach,
                                    List<ExportRow> attested) {
        Sort parsed = JavaSmtSorts.sortOfJava(attach.javaType());
        for (ExportRow export : attested) {
            Term delivered = composedFamilies.lower(export.sessionId(),
                    export.expressionRef(), "paired-arm", null);
            if (delivered == null) continue;
            if (lowering.leafEquals(attach.symbol(), parsed,
                    attach.javaType(), delivered, export.javaType()) == null) {
                lowering.leafUnrelated(attach.symbol(), parsed,
                        delivered.sort);
                continue;
            }
            lowering.declareStated(attach.symbol(), parsed == Sort.VALUE
                    ? delivered.sort : parsed);
            return true;
        }
        return false;
    }

    private Term arrived(AttachRow attach) {
        return lowering.statedValue(VmTermLowering.received(attach),
                attach.javaType());
    }

    void frames(String session, Set<String> reached) {
        SmtLowering.SessionJoin join = corpus.join(session);
        for (String occurrenceId : reached) {
            SmtLowering.RefusalFrame frame = join.frame(occurrenceId);
            if (frame == null) continue;
            List<String> moving = new ArrayList<String>(
                    lowering.frameMovers(frame));
            boolean moves = !moving.isEmpty();
            pathConcrete.put("frame:" + occurrenceId, new Concrete(moves
                    ? SmtLowering.Unbound.FREE : SmtLowering.Unbound.HELD,
                    occurrenceId, frame.producer, moves ? "its run computed "
                    + "on an arrival it refused, whose producer rests on "
                    + "what can move: every write of it a read joins is free"
                    : frame.producer.isEmpty()
                    ? SmtLowering.Unbound.PRODUCER_UNSTATED + ": its run "
                    + "computed on an arrival it refused, and no export row "
                    + "of this session states the refused handle ("
                    + frame.refusal + ")"
                    : "its run computed on an arrival it refused, whose "
                    + "producer rests on nothing that moves", moving));
        }
    }

    public static final class Concrete {
        public final String kind;
        public final String subject;
        public final String value;
        public final String reason;
        public final List<String> movesWith;
        public final String pathId;
        public final String arm;

        Concrete(String kind, String subject, String value, String reason,
                 List<String> movesWith) {
            this(kind, subject, value, reason, movesWith, "", "");
        }

        private Concrete(String kind, String subject, String value,
                         String reason, List<String> movesWith,
                         String pathId, String arm) {
            this.kind = kind;
            this.subject = subject;
            this.value = value;
            this.reason = reason;
            this.movesWith = Collections.unmodifiableList(movesWith);
            this.pathId = pathId;
            this.arm = arm == null || arm.isEmpty() ? null : arm;
        }

        Concrete on(String path) {
            return new Concrete(kind, subject, value, reason, movesWith,
                    path, arm);
        }

        Concrete in(String selector) {
            return new Concrete(kind, subject, value, reason, movesWith,
                    pathId, selector);
        }
    }

    List<String> closureConditions(String session,
                                   Map<String, Long> reached,
                                   Independence relevant,
                                   List<GapRow> refusals) {
        List<String> conditions = new ArrayList<String>();
        for (Map.Entry<String, Long> entry : reached.entrySet()) {
            if (anchor.id().equals(entry.getKey())) continue;
            OccurrenceAddress at = corpus.occurrence(entry.getKey());
            if (at == null) continue;
            conditions.addAll(prefix(corpus.decisionsOf(session, at),
                    entry.getValue().longValue(), "join-pi ", relevant,
                    refusals));
        }
        return conditions;
    }

    private Set<String> pinnedOwners(String session,
                                     Map<String, Long> reached,
                                     Set<String> moved,
                                     Set<String> repaired) {
        Set<String> pinned = new LinkedHashSet<String>();
        for (String key : containerOwners(session, reached, moved)) {
            if (repaired.contains(key) && pinned.add(key)) {
                gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        "OWNER_PINNED_BY_CONTAINER_READ:" + key + "@"
                                + session, "a field or a query of this path "
                                + "is asked through a query's read of this "
                                + "container, which names no object, so its "
                                + "family is held to the arm the run took");
            }
        }
        for (Map.Entry<String, Long> at : reached.entrySet()) {
            OccurrenceAddress occurrence = corpus.occurrence(at.getKey());
            if (occurrence == null) continue;
            for (WriteRow write : corpus.writesOn(session, occurrence)) {
                if (write.seq() > at.getValue()
                        || write.location().kind() != LocationKind.MAP) {
                    continue;
                }
                JsonObject mutation = corpus.expression(session,
                        write.expressionRef());
                String key = movedOwner(mutation, moved);
                if (key != null && repaired.contains(key)
                        && pinned.add(key)) {
                    gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                            "OWNER_PINNED_BY_MUTATION:" + key + "@"
                                    + session, "a reader of this path "
                                    + "mutated a container through this "
                                    + "reference, so its family is held to "
                                    + "the arm the run took: another pairing "
                                    + "would mutate an object no row "
                                    + "records the mutation of");
                }
            }
        }
        for (String key : repaired) {
            for (WriteRow store : corpus.writesOf(session, key)) {
                if (store.referentState() == null
                        && store.referentStateRefused() == null
                        || storesItsContainer(session, store)) {
                    continue;
                }
                if (pinned.add(key)) {
                    gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                            "OWNER_PINNED_BY_WRAPPER:" + key + "@" + session,
                            "the store at version " + store.version()
                                    + " holds a container through an object"
                                    + " that is not it, and a query through"
                                    + " such an object names no owner, so "
                                    + "this family is held to the arm the "
                                    + "run took");
                }
                break;
            }
        }
        return pinned;
    }

    private Set<String> containerOwners(String session,
                                        Map<String, Long> reached,
                                        Set<String> moved) {
        Set<String> owners = new LinkedHashSet<String>();
        Set<JsonElement> walked = ExpressionWalk.identitySet();
        Map<String, Long> asked = new LinkedHashMap<String, Long>(reached);
        TargetRow anchored = corpus.target(session, anchor);
        if (anchored != null) {
            asked.merge(anchor.id(), anchored.seq(), Math::max);
        }
        for (Map.Entry<String, Long> at : asked.entrySet()) {
            OccurrenceAddress occurrence = corpus.occurrence(at.getKey());
            if (occurrence == null) continue;
            StringBuilder terms = new StringBuilder();
            for (DecisionRow decision : corpus.decisionsOf(session,
                    occurrence)) {
                if (decision.seq() <= at.getValue()) {
                    terms.append(decision.term()).append(' ');
                }
            }
            for (WriteRow write : corpus.writesOn(session, occurrence)) {
                if (write.seq() <= at.getValue()) {
                    terms.append(write.expressionRef()).append(' ');
                }
            }
            TargetRow target = corpus.target(session, occurrence);
            if (target != null) terms.append(target.phiTerm());
            Matcher refs = EXPRESSION_REF.matcher(terms);
            while (refs.find()) {
                for (ExpressionWalk walk = ExpressionWalk.of(corpus.expression(
                        session, refs.group()), walked); walk.hasNext(); ) {
                    String key = movedOwner(walk.next(), moved);
                    if (key != null
                            && key.startsWith(LocationKind.MAP + "/")) {
                        owners.add(key);
                    }
                }
            }
        }
        return owners;
    }

    private static final Pattern EXPRESSION_REF =
            Pattern.compile("EXPR\\.[0-9a-f]+");

    private static String movedOwner(JsonObject node, Set<String> moved) {
        JsonElement owner = RestsOn.unwrapped(node == null ? null
                : node.get("owner"));
        if (!VmRows.GUARDED_READ_TYPE.equals(VmExpressionIr.typeOf(owner))) {
            return null;
        }
        JsonObject read = owner.getAsJsonObject();
        String key = SmtLowering.locationKey(JsonFields.object(read,
                "location"));
        return moved.contains(SmtLowering.readKey(key,
                VmRows.readEvent(read))) ? key : null;
    }

    private boolean storesItsContainer(String session, WriteRow store) {
        JsonElement stored = RestsOn.unwrapped(corpus.expression(session,
                store.expressionRef()));
        if (!SmtLowering.named(stored)) return false;
        String rid = Long.toString(VmRows.referencedObjectRid(
                stored.getAsJsonObject().get("_exp").getAsString()));
        return store.referentState() != null
                ? rid.equals(store.referentState().location().owner())
                : !corpus.writesOf(session, SmtLowering.locationKey(
                LocationId.of(LocationKind.MAP, rid, "-3"))).isEmpty();
    }

    private Set<String> familyBound(String session, List<ReadRow> moving) {
        Set<String> bound = new LinkedHashSet<String>();
        for (AttachRow attach : corpus.attachesOn(session, anchor)) {
            bound.add(attach.symbol());
        }
        for (ReadRow read : moving) {
            bound.add(Independence.location(SmtLowering.locationKey(
                    read.location())));
            if (!read.symbol().isEmpty()) bound.add(read.symbol());
        }
        return bound;
    }

    private static final class Repairing {
        final List<ReadRow> reads = new ArrayList<ReadRow>();
        final Set<String> keys = new LinkedHashSet<String>();
        final Map<String, String> planted =
                new LinkedHashMap<String, String>();
        Set<String> pinned = Collections.emptySet();
    }

    private Repairing repairing(String session, Map<String, Long> reached,
                                long cutoff, Set<Long> phiReads) {
        Map<String, String> pairings = corpus.world(session).pairings;
        Map<String, String> planted = new LinkedHashMap<String, String>();
        Set<String> plantedBlocks = new LinkedHashSet<String>();
        SessionReader reader = corpus.session(session);
        List<ReadRow> sessionReads = reader == null
                ? Collections.<ReadRow>emptyList() : reader.reads();
        for (ReadRow read : pairings.isEmpty()
                ? Collections.<ReadRow>emptyList() : sessionReads) {
            String writer = pairings.get(Confirmation.id(read.endpoint()));
            if (writer == null) continue;
            String key = SmtLowering.locationKey(read.location());
            for (WriteRow write : corpus.join(session).writes(key)) {
                if (writer.equals(Confirmation.writer(write))) {
                    planted.put(key, ComposedFamilies.writer(write));
                    plantedBlocks.add(block(read));
                    break;
                }
            }
        }
        Map<String, List<ReadRow>> blocks =
                new LinkedHashMap<String, List<ReadRow>>();
        for (ReadRow read : sessionReads) {
            boolean atAnchor = anchor.id().equals(
                    read.endpoint().occurrence().id())
                    && (read.seq() <= cutoff
                    || phiReads.contains(Long.valueOf(read.seq())));
            if (atAnchor || plantedBlocks.contains(block(read))) {
                blocks.computeIfAbsent(block(read),
                        key -> new ArrayList<ReadRow>()).add(read);
            }
        }
        Set<String> locations = new LinkedHashSet<String>();
        List<ReadRow> admitted = new ArrayList<ReadRow>();
        for (List<ReadRow> block : blocks.values()) {
            if (!anotherWriter(session, block)) continue;
            locations.add(SmtLowering.locationKey(block.get(0).location()));
            admitted.addAll(block);
        }
        Set<String> keys = new LinkedHashSet<String>();
        for (ReadRow read : admitted) keys.add(key(read));
        Repairing repairing = new Repairing();
        repairing.pinned = pinnedOwners(session, reached, keys, locations);
        for (ReadRow read : admitted) {
            String key = SmtLowering.locationKey(read.location());
            if (repairing.pinned.contains(key)) continue;
            repairing.reads.add(read);
            repairing.keys.add(key(read));
            if (planted.containsKey(key)) {
                repairing.planted.put(key, planted.get(key));
            }
        }
        return repairing;
    }

    private static String block(ReadRow read) {
        return read.endpoint().occurrence().id() + "|"
                + SmtLowering.locationKey(read.location());
    }

    private static String key(ReadRow read) {
        return SmtLowering.readKey(SmtLowering.locationKey(read.location()),
                read.seq());
    }

    private boolean anotherWriter(String session, List<ReadRow> block) {
        return anotherWriter(corpus, session, block);
    }

    private static boolean anotherWriter(Corpus corpus, String session,
                                         List<ReadRow> block) {
        Set<Long> asked = new LinkedHashSet<Long>();
        for (ReadRow read : block) {
            long version = read.observedVersion();
            if (version < 0L || !Arms.namedOwner(read.location())
                    || !asked.add(version)) {
                continue;
            }
            String key = SmtLowering.locationKey(read.location());
            WriteRow observed = corpus.writeOf(session, key, version);
            String seen = observed == null ? null
                    : ComposedFamilies.writer(observed);
            for (WriteRow write : corpus.eligibleWrites(session, key,
                    version, read.endpoint().occurrence())) {
                if (!ComposedFamilies.writer(write).equals(seen)) return true;
            }
        }
        return false;
    }

    private List<String> prefix(List<DecisionRow> decisions, long before,
                                String kind, Independence relevant,
                                List<GapRow> refusals) {
        List<String> conditions = new ArrayList<String>();
        for (DecisionRow decision : decisions) {
            if (decision.seq() >= before) continue;
            if (!relevant.keeps(decision)) continue;
            String subject = kind + decision.siteId() + "#"
                    + decision.ordinal();
            String conjunct = lowering.statedTerm(Arms.conjunct(decision),
                    "pi:" + subject);
            if (!Arms.predicate(conjunct)) continue;
            if (unknown(conjunct, refusals, subject)) continue;
            conditions.add(conjunct);
        }
        return conditions;
    }

    void statedReads(String session, Set<String> occurrences,
                     Independence relevant, SmtLowering.SessionJoin join,
                     List<GapRow> refusals, Map<String, String> joins,
                     Set<String> answered) {
        for (ReadRow read : restsOn.statedRows(session, occurrences)) {
            if (read.symbol() == null || read.symbol().isEmpty()) continue;
            if (!relevant.keeps(read)) continue;
            if (joins.containsKey(read.symbol())) continue;
            if (joinable(session, read)) continue;
            if (!"".equals(SmtLowering.mintedReadSymbol(join,
                    read.observedVersion()))) {
                continue;
            }
            if (!pin(session, read, refusals, joins, answered)
                    || !joins.containsKey(read.symbol())) {
                continue;
            }
            String subject = SmtLowering.locationKey(read.location()) + "@"
                    + read.observedVersion();
            if (corpus.uncaptured(session)) {
                joins.put(read.symbol(), "true");
                lowering.freedUncaptured(subject);
            } else {
                lowering.held(subject, read.concreteValue(),
                        "no write row states the version this read saw");
            }
        }
    }

    private boolean pin(String session, ReadRow read,
                        List<GapRow> refusals, Map<String, String> joins,
                        Set<String> answered) {
        String text = read.concreteValue() == null ? ""
                : read.concreteValue().trim();
        if (text.isEmpty()) return false;
        answered.add(read.symbol());
        Term value = lowering.statedValue(text, read.javaType());
        if (value == null) {
            refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, read.symbol(),
                    "the row states the value \"" + text + "\" at Java "
                            + "type \"" + (read.javaType() == null ? ""
                            : read.javaType()) + "\", which this lowering "
                            + "places nowhere"));
            return true;
        }
        lowering.pin(read.symbol(), value.sort);
        joins.put(read.symbol(), "(= " + read.symbol() + " " + value.text
                + ")");
        return true;
    }

    private boolean joinable(String session, ReadRow read) {
        return read.observedVersion() >= 0L
                && corpus.writeOf(session,
                SmtLowering.locationKey(read.location()),
                read.observedVersion()) != null;
    }

    void stateJoins(String session, Set<String> occurrences,
                    Independence relevant, SmtLowering.SessionJoin join,
                    List<GapRow> refusals, List<ReadRow> joined,
                    Map<String, String> joins, Set<String> answered) {
        for (ReadRow read : restsOn.statedRows(session, occurrences)) {
            if (read.symbol() == null || read.symbol().isEmpty()) continue;
            if (!relevant.keeps(read)) continue;
            String key = SmtLowering.locationKey(read.location());
            boolean atAnchor = anchor.id().equals(
                    read.endpoint().occurrence().id())
                    || join.repaired(key, read.seq());
            long version = read.observedVersion();
            WriteRow write = corpus.writeOf(session, key, version);
            if (joins.containsKey(read.symbol())) {
                if (atAnchor && write == null && version >= 0L
                        && "".equals(SmtLowering.mintedReadSymbol(join,
                        version))) {
                    joined.add(read);
                }
                continue;
            }
            if (write != null && corpus.expression(session,
                    write.expressionRef()) == null) {
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.DIAGNOSTIC, write.expressionRef(),
                        "a write row of " + key + "@" + version + " cites an "
                                + "expression its session's table does not "
                                + "hold, so the chain this read joins to is "
                                + "not in this corpus"));
                continue;
            }
            SmtLowering.Binder<Boolean> binder = new SmtLowering.Binder<Boolean>() {
                @Override
                public Term join(JsonElement value) {
                    return lowering.dispatch(value, SmtLowering.whole(value,
                            null), "state-join:" + key + "@" + version);
                }

                @Override
                public Boolean joined(Term value) {
                    lowering.declareStated(read.symbol(), value.sort);
                    String equals = "(= " + read.symbol() + " " + value.text
                            + ")";
                    joins.put(read.symbol(), "true".equals(value.precondition)
                            ? equals : "(and " + equals + " "
                            + value.precondition + ")");
                    if (atAnchor) joined.add(read);
                    return true;
                }

                @Override
                public Boolean minted(String symbol) {
                    return mint(session, read, symbol, refusals, joins);
                }

                @Override
                public Boolean pinned() {
                    if (!answered.contains(read.symbol())
                            && !pin(session, read, refusals, joins,
                            answered)) {
                        return null;
                    }
                    return joins.containsKey(read.symbol());
                }

                @Override
                public String returned() {
                    return read.concreteValue() == null ? ""
                            : read.concreteValue().trim();
                }

                @Override
                public Boolean free() {
                    lowering.declareStated(read.symbol(),
                            JavaSmtSorts.sortOfJava(read.javaType()));
                    return true;
                }

                @Override
                public Boolean refused(Term value, String subject,
                                       String detail) {
                    lowering.declareStated(read.symbol(),
                            JavaSmtSorts.sortOfJava(read.javaType()));
                    gaps.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                            GapClass.DIAGNOSTIC, key + "@" + version,
                            detail + ": the read is free, over-approximated"));
                    return true;
                }
            };
            List<String> own = lowering.ownConditions(
                    () -> lowering.bind(key, version, read.seq(), null,
                            binder)
                            && joins.containsKey(read.symbol()));
            if (!own.isEmpty()) {
                own.add(0, joins.get(read.symbol()));
                joins.put(read.symbol(), VmTermLowering.and(own));
            }
        }
    }

    private boolean mint(String session, ReadRow read, String minted,
                         List<GapRow> refusals, Map<String, String> joins) {
        if (minted.equals(read.symbol())) return true;
        Sort sort = lowering.declaredSort(minted);
        RootMintRow root = corpus.rootBySymbol(session, minted);
        if (sort == null && root != null) {
            sort = corpus.declaredSymbols().get(minted);
        }
        if (sort == null || (!lowering.stated(minted) && root == null)) {
            refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, minted,
                    "the read row that states this version's symbol states "
                            + "no value for it, and no root of this session "
                            + "mints it, so nothing binds it"));
            return false;
        }
        if (root != null && !lowering.stated(minted)) {
            lowering.declareStated(minted, sort);
        }
        lowering.declareStated(read.symbol(), sort);
        joins.put(read.symbol(), "(= " + read.symbol() + " " + minted + ")");
        return true;
    }

    private List<String> arrivals(List<AttachRow> attaches) {
        List<String> stated = new ArrayList<String>();
        Set<String> seen = new LinkedHashSet<String>();
        for (AttachRow attach : attaches) {
            if (!seen.add(attach.symbol())) continue;
            Term received = arrived(attach);
            if (received == null) continue;
            stated.add("(= " + attach.symbol() + " " + received.text + ")");
        }
        return stated;
    }


    private void domains() {
        int ordinal = 0;
        for (Map.Entry<String, List<RootMintRow>> entry
                : corpus.roots().entrySet()) {
            RootMintRow row = seedRow(entry.getValue());
            if (row.kind() == RootKind.CLOCK) continue;
            RootDomain domain = domainOf(row);
            roots.put(row.rootId(), domain);
            if (!lowering.declared(row.symbol())) continue;
            if (row.kind() == RootKind.MARKER && row.declared()) continue;
            if (corpus.varied(row.rootId())) {
                gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        row.rootId(), "sessions of this corpus recorded "
                                + "this root at different values, so its "
                                + "domain is stated per path and not once");
                continue;
            }
            String min = domain.min();
            String max = domain.max();
            if (min != null && max != null && !min.isEmpty()
                    && !max.isEmpty()) {
                lowering.assertNamed("root_domain__" + ordinal++,
                        window(row.symbol(), min, max));
                continue;
            }
            if (placeholder(row)) {
                gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                        row.rootId(), "placeholder published as root: this "
                                + "symbol is also a read of session "
                                + row.sessionId() + ", so the read states "
                                + "what it is and the mint pins nothing");
                continue;
            }
            String literal = smtLiteral(row.recordedValue(), sortOf(row));
            if (literal.isEmpty()) continue;
            lowering.assertNamed("root_domain__" + ordinal++,
                    "(= " + row.symbol() + " " + literal + ")");
        }
    }

    private boolean placeholder(RootMintRow row) {
        if (row.declared()) return false;
        RootDomain domain = domainOf(row);
        if (!domain.pinned()) return false;
        for (RootMintRow mint : corpus.roots().get(row.rootId())) {
            if (corpus.read(mint.sessionId(), mint.symbol()) != null) {
                return true;
            }
        }
        return false;
    }

    private void clocks(List<String> cells, Map<String, Long> readings,
                        Map<String, Long> ticks,
                        Map<String, String> earlierOf) {
        List<RootMintRow> clocks = new ArrayList<RootMintRow>();
        for (Map.Entry<String, List<RootMintRow>> entry
                : corpus.roots().entrySet()) {
            RootMintRow row = seedRow(entry.getValue());
            if (row.kind() != RootKind.CLOCK
                    || !lowering.declared(row.symbol())) {
                continue;
            }
            if (instant(row) == null) continue;
            clocks.add(row);
        }
        List<RootMintRow> placedCells = new ArrayList<RootMintRow>();
        for (RootMintRow row : clocks) {
            Long placed = clockTimeline.get(row.rootId());
            if (placed == null) {
                gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                        row.rootId(), "this clock cell has no instant on the "
                                + "recording's timeline (the recording never "
                                + "read it, and no session that read it read "
                                + "a cell of the same clock the recording "
                                + "read) and reaches the formula though the "
                                + "paths naming it were refused, so it has "
                                + "no domain and no order");
                continue;
            }
            readings.put(row.symbol(), placed);
            long reading = placed;
            String instant = Long.toString(reading);
            placedCells.add(row);
            ticks.put(row.symbol(), row.clockNanos());
            RootDomain domain = corpus.domainOf(row, instant);
            String floor = domain.min() == null ? instant
                    : integralLiteral(domain.min());
            String ceiling = domain.max() == null
                    ? JavaPrimitiveSmtSemantics.clockSkewCeiling(instant,
                            row.clockNanos())
                    : integralLiteral(domain.max());
            roots.put(row.rootId(), RootDomain.of(row.rootId(),
                    RootKind.CLOCK, instant, floor, ceiling));
            lowering.assertNamed("clock_domain__"
                            + ArtifactIO.digest(row.symbol(), 10),
                    JavaPrimitiveSmtSemantics.clockDomain(row.symbol(),
                            floor, ceiling));
            if (row.clock().source().isEmpty()) {
                gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                        row.rootId(), "this clock cell's row states no JVM "
                                + "clock it reads, so it is on no clock's "
                                + "order: no cell runs on from it, and it "
                                + "from none");
            }
        }
        Map<NodeId, List<RootMintRow>> byNode =
                new LinkedHashMap<NodeId, List<RootMintRow>>();
        for (RootMintRow row : placedCells) {
            byNode.computeIfAbsent(row.occurrence().node(),
                    node -> new ArrayList<RootMintRow>()).add(row);
        }
        placedCells.sort(Comparator.comparingLong(RootMintRow::seq)
                .thenComparing(RootMintRow::symbol));
        for (RootMintRow row : placedCells) cells.add(row.symbol());
        for (List<RootMintRow> mints : byNode.values()) {
            mints.sort(Comparator.comparingLong(RootMintRow::seq));
            for (int index = 1; index < mints.size(); index++) {
                String later = mints.get(index).symbol();
                long reading = readings.get(later);
                for (int before = index - 1; before >= 0; before--) {
                    String earlier = mints.get(before).symbol();
                    long earlierReading = readings.get(earlier);
                    if (!mints.get(index).clock().same(
                            mints.get(before).clock())) {
                        continue;
                    }
                    long inversion = earlierReading - reading;
                    lowering.assertNamed("clock_order__" + ArtifactIO.digest(
                                    earlier + "|" + later, 10),
                            inversion <= 0L
                                    ? "(<= " + earlier + " " + later + ")"
                                    : "(<= (- " + earlier + " " + later
                                    + ") " + integralLiteral(
                                            Long.toString(inversion)) + ")");
                    earlierOf.put(later, earlier);
                    break;
                }
            }
        }
    }

    private Long instant(RootMintRow row) {
        Long reading = number(row.hostReading());
        if (reading == null) {
            gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    row.rootId(), "the mint of this clock cell states no "
                            + "instant (" + row.recordedValue() + "), so it "
                            + "has no domain and no reading");
        }
        return reading;
    }

    private Map<String, Map<String, Long>> clockBases() {
        String seed = seed();
        Map<String, Map<String, Long>> bases =
                new LinkedHashMap<String, Map<String, Long>>();
        if (seed == null) return bases;
        Map<String, List<RootMintRow>> bySession =
                new LinkedHashMap<String, List<RootMintRow>>();
        for (List<RootMintRow> rows : corpus.roots().values()) {
            for (RootMintRow row : rows) {
                if (row.kind() == RootKind.CLOCK
                        && !row.sessionId().equals(seed)) {
                    bySession.computeIfAbsent(row.sessionId(),
                            session -> new ArrayList<RootMintRow>()).add(row);
                }
            }
        }
        for (Map.Entry<String, List<RootMintRow>> session
                : bySession.entrySet()) {
            Map<RootMintRow, Long> anchored =
                    new LinkedHashMap<RootMintRow, Long>();
            for (RootMintRow row : session.getValue()) {
                RootMintRow recorded = corpus.rootOf(seed, row.rootId());
                Long host = number(row.hostReading());
                Long reading = recorded == null ? null
                        : number(recorded.hostReading());
                if (host != null && reading != null) {
                    anchored.put(row, host - reading);
                }
            }
            Map<String, Long> late = new LinkedHashMap<String, Long>();
            for (RootMintRow row : session.getValue()) {
                Long base = anchored.get(row);
                if (base == null) {
                    RootMintRow nearest = null;
                    for (RootMintRow anchor : anchored.keySet()) {
                        if (!anchor.occurrence().node().equals(
                                row.occurrence().node())
                                || row.clock() == null
                                || !row.clock().same(anchor.clock())) {
                            continue;
                        }
                        long distance = Math.abs(anchor.seq() - row.seq());
                        if (nearest == null || distance
                                < Math.abs(nearest.seq() - row.seq())
                                || (distance == Math.abs(nearest.seq()
                                - row.seq()) && anchor.seq() < nearest.seq())) {
                            nearest = anchor;
                        }
                    }
                    base = nearest == null ? null : anchored.get(nearest);
                }
                if (base != null && base != 0L) late.put(row.symbol(), base);
            }
            if (!late.isEmpty()) bases.put(session.getKey(), late);
        }
        return bases;
    }

    private void placeClocks() {
        String seed = seed();
        List<RootMintRow> read = new ArrayList<RootMintRow>();
        Map<String, Long> readings = new LinkedHashMap<String, Long>();
        for (List<RootMintRow> rows : corpus.roots().values()) {
            RootMintRow row = seedRow(rows);
            Long reading = number(row.hostReading());
            if (row.kind() != RootKind.CLOCK || reading == null
                    || !row.sessionId().equals(seed)) {
                continue;
            }
            readings.put(row.symbol(), reading);
            read.add(row);
            clockTimeline.put(row.rootId(), reading);
        }
        for (List<RootMintRow> rows : corpus.roots().values()) {
            RootMintRow row = seedRow(rows);
            if (row.kind() != RootKind.CLOCK
                    || clockTimeline.containsKey(row.rootId())
                    || number(row.hostReading()) == null) {
                continue;
            }
            Long reading = placed(rows, read, readings);
            if (reading != null) {
                clockTimeline.put(row.rootId(), reading);
                continue;
            }
            for (RootMintRow mint : rows) {
                unplacedClocks.put(mint.symbol(), mint.rootId());
            }
        }
    }

    private Long placed(List<RootMintRow> rows, List<RootMintRow> read,
                        Map<String, Long> readings) {
        for (RootMintRow cell : rows) {
            Long host = number(cell.hostReading());
            if (cell.kind() != RootKind.CLOCK || host == null) continue;
            RootMintRow nearest = null;
            long from = 0L;
            for (RootMintRow anchor : read) {
                RootMintRow same = corpus.rootOf(cell.sessionId(),
                        anchor.rootId());
                Long sameHost = same == null ? null
                        : number(same.hostReading());
                if (sameHost == null || !anchor.occurrence().node().equals(
                        cell.occurrence().node())
                        || !cell.clock().same(same.clock())) {
                    continue;
                }
                long distance = Math.abs(anchor.seq() - cell.seq());
                long best = nearest == null ? Long.MAX_VALUE
                        : Math.abs(nearest.seq() - cell.seq());
                if (distance < best || (distance == best
                        && anchor.seq() < nearest.seq())) {
                    nearest = anchor;
                    from = sameHost;
                }
            }
            if (nearest != null) {
                return readings.get(nearest.symbol()) + (host - from);
            }
        }
        return null;
    }

    private static Long number(String text) {
        try {
            return Long.valueOf(text.trim());
        } catch (NumberFormatException notAnInstant) {
            return null;
        }
    }

    private String seed() {
        String stated = corpus.seedSessionId();
        return stated == null || stated.isEmpty() ? null : stated;
    }

    private RootMintRow seedRow(List<RootMintRow> rows) {
        String seed = seed();
        if (seed != null) {
            for (RootMintRow row : rows) {
                if (row.sessionId().equals(seed)) return row;
            }
        }
        return rows.get(0);
    }

    private void refutations(List<Disjunct> disjuncts,
                             List<String> clockCells,
                             Map<String, Long> clockReadings,
                             Map<String, String> clockBefore) {
        List<Refutations.Refuted> refuted;
        try {
            refuted = Refutations.read(corpus.iteration());
        } catch (java.io.IOException | RuntimeException unreadable) {
            gap(GapKind.CLAIM_REFUTED, GapClass.DIAGNOSTIC, Refutations.FILE,
                    "this iteration's refuted claims could not be read, so"
                            + " none is excluded: " + unreadable);
            return;
        }
        int ordinal = 0;
        for (Refutations.Refuted model : refuted) {
            String path = null;
            for (Disjunct disjunct : disjuncts) {
                if (disjunct.path().pathId.equals(model.pathId)) {
                    path = disjunct.selector();
                }
            }
            if (path == null) continue;
            List<String> conjuncts = new ArrayList<String>();
            conjuncts.add(path);
            boolean composed = true;
            for (String arm : model.arms) {
                String here = Refutations.atPath(arm,
                        Refutations.ordinal(path));
                composed &= lowering.declared(here);
                conjuncts.add(here);
            }
            if (!composed) continue;
            Map<String, String> pinned = new LinkedHashMap<String, String>();
            for (Map.Entry<String, String> root
                    : model.assignment.entrySet()) {
                RootMintRow row = corpus.anyRoot(root.getKey());
                if (row == null || row.kind() == RootKind.CLOCK) continue;
                pinned.put(row.symbol(), smtLiteral(root.getValue(),
                        sortOf(row)));
            }
            for (Map.Entry<String, String> pin : pinned.entrySet()) {
                if (pin.getValue().isEmpty()
                        || !lowering.declared(pin.getKey())) {
                    continue;
                }
                conjuncts.add("(= " + pin.getKey() + " " + pin.getValue()
                        + ")");
            }
            Map<String, Long> skews = new LinkedHashMap<String, Long>();
            for (String cell : clockCells) {
                String before = clockBefore.get(cell);
                Long previous = before == null ? Long.valueOf(0L)
                        : skews.get(before);
                Long skew = previous;
                String instant = model.moved.get(cell);
                if (instant != null) {
                    try {
                        skew = Long.parseLong(Composition.modelValue(instant))
                                - clockReadings.get(cell);
                    } catch (NumberFormatException notAnInstant) {
                        skew = null;
                    }
                }
                skews.put(cell, skew);
                if (skew == null || previous == null
                        || !lowering.declared(cell) || (before != null
                        && !lowering.declared(before))) {
                    continue;
                }
                conjuncts.add(clockStep(cell, clockReadings, clockBefore,
                        Long.signum(skew - previous)));
            }
            String name = REFUTED_CLAIM + ordinal++;
            lowering.assertNamed(name,
                    "(not " + VmTermLowering.and(conjuncts) + ")");
            refutationNames.put(name, model);
            gap(GapKind.CLAIM_REFUTED, GapClass.DIAGNOSTIC, model.pathId,
                    "CONFIRM refuted the model on this path with arms "
                            + model.arms + " at " + model.assignment
                            + (model.moved.isEmpty() ? ""
                            : " moving " + model.moved)
                            + ", so it is excluded: " + model.reason);
        }
    }

    static String clockStep(String cell, Map<String, Long> readings,
                            Map<String, String> before, int sign) {
        return clockStep(cell, readings, before,
                sign == 0 ? "=" : sign > 0 ? ">" : "<", 0L);
    }

    static String clockStep(String cell, Map<String, Long> readings,
                            Map<String, String> before, String relation,
                            long offset) {
        String reading = integralLiteral(Long.toString(readings.get(cell)));
        String previous = before.get(cell);
        if (offset != 0L) {
            String skew = "(- " + cell + " " + reading + ")";
            return "(" + relation + " " + (previous == null ? skew
                    : "(- " + skew + " (- " + previous + " "
                    + integralLiteral(Long.toString(readings.get(previous)))
                    + "))") + " " + integralLiteral(Long.toString(offset))
                    + ")";
        }
        return previous == null
                ? "(" + relation + " " + cell + " " + reading + ")"
                : "(" + relation + " (- " + cell + " " + reading + ") (- "
                + previous + " " + integralLiteral(Long.toString(
                readings.get(previous))) + "))";
    }

    private RootDomain domainOf(RootMintRow row) {
        return RootDomain.widened(row,
                corpus.declaredDomain(row.rootId()) != null)
                ? corpus.domainOf(row)
                : corpus.domainOf(row, row.recordedValue());
    }

    private List<Valuation> valuations() {
        List<String> declared = new ArrayList<String>();
        Map<String, List<String>> alternatives =
                new LinkedHashMap<String, List<String>>();
        for (Map.Entry<String, RootDomain> entry : roots.entrySet()) {
            RootDomain domain = entry.getValue();
            if (domain.kind() == RootKind.CLOCK) continue;
            RootMintRow row = corpus.anyRoot(entry.getKey());
            if (row == null || !row.declared()) continue;
            if (!lowering.declared(row.symbol())) {
                gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                        entry.getKey(), "the case declares this root and no "
                                + "admitted path's formula names it, so no "
                                + "valuation of it was asked");
                continue;
            }
            List<String> values = alternativesOf(domain);
            if (values.isEmpty()) {
                if (domain.kind() == RootKind.MARKER) {
                    gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                            entry.getKey(), "a declared marker is free in "
                                    + "{recorded, flipped} by its kind, and "
                                    + "this mint states \""
                                    + domain.recordedValue()
                                    + "\", which is neither polarity, so "
                                    + "there is no flip to ask");
                }
                continue;
            }
            declared.add(entry.getKey());
            declaredRoots.put(entry.getKey(), row);
            alternatives.put(entry.getKey(), values);
        }
        List<Valuation> valuations = new ArrayList<Valuation>();
        Map<String, String> recorded = new LinkedHashMap<String, String>();
        for (String rootId : declared) {
            recorded.put(rootId, roots.get(rootId).recordedValue());
        }
        valuations.add(valuation(0, recorded,
                Collections.<String, String>emptyMap()));
        List<Map<String, String>> moves = new ArrayList<Map<String, String>>();
        for (String rootId : declared) {
            for (String value : alternatives.get(rootId)) {
                Map<String, String> move = new LinkedHashMap<String, String>();
                move.put(rootId, value);
                moves.add(move);
            }
        }
        moves.sort(Comparator.comparingInt(this::tier)
                .thenComparingLong(this::distance)
                .thenComparing(move -> configurationOnly(move.keySet(),
                        rootId -> corpus.anyRoot(rootId).category())));
        List<Map<String, String>> pairs =
                new ArrayList<Map<String, String>>();
        for (int first = 0; first < moves.size(); first++) {
            for (int second = first + 1; second < moves.size(); second++) {
                Map<String, String> left = moves.get(first);
                Map<String, String> right = moves.get(second);
                String leftRoot = left.keySet().iterator().next();
                String rightRoot = right.keySet().iterator().next();
                if (leftRoot.equals(rightRoot)) continue;
                Map<String, String> pair =
                        new LinkedHashMap<String, String>(left);
                pair.putAll(right);
                pairs.add(pair);
            }
        }
        moves.addAll(pairs);
        int ordinal = 1;
        for (Map<String, String> move : moves) {
            if (valuations.size() >= maxValuations) break;
            Map<String, String> assignment =
                    new LinkedHashMap<String, String>(recorded);
            assignment.putAll(move);
            valuations.add(valuation(ordinal++, assignment, move));
        }
        return valuations;
    }

    static boolean configurationOnly(Collection<String> moved,
                                     java.util.function.Function<String,
                                             RootCategory> categoryOf) {
        if (moved.isEmpty()) return false;
        for (String key : moved) {
            if (categoryOf.apply(key) != RootCategory.CONFIG) return false;
        }
        return true;
    }

    private int tier(Map<String, String> move) {
        for (Map.Entry<String, String> entry : move.entrySet()) {
            RootDomain domain = roots.get(entry.getKey());
            if (domain == null || domain.kind() == RootKind.MARKER) continue;
            String value = entry.getValue().trim();
            if (integralLiteral(value).isEmpty()
                    || !anchors(domain).contains(new BigInteger(value))) {
                return 1;
            }
        }
        return 0;
    }

    private static Set<BigInteger> anchors(RootDomain domain) {
        Set<BigInteger> anchors = new LinkedHashSet<BigInteger>();
        if (domain.min() == null || domain.max() == null
                || integralLiteral(domain.min()).isEmpty()
                || integralLiteral(domain.max()).isEmpty()) {
            return anchors;
        }
        BigInteger low = new BigInteger(domain.min().trim());
        BigInteger high = new BigInteger(domain.max().trim());
        for (int step = 0; step <= 2; step++) {
            BigInteger up = low.add(BigInteger.valueOf(step));
            BigInteger down = high.subtract(BigInteger.valueOf(step));
            if (up.compareTo(high) <= 0) anchors.add(up);
            if (down.compareTo(low) >= 0) anchors.add(down);
        }
        return anchors;
    }

    private long distance(Map<String, String> move) {
        long total = 0L;
        for (Map.Entry<String, String> entry : move.entrySet()) {
            RootDomain domain = roots.get(entry.getKey());
            if (domain == null) continue;
            String moved = entry.getValue().trim();
            String recorded = domain.recordedValue().trim();
            if (integralLiteral(moved).isEmpty()
                    || integralLiteral(recorded).isEmpty()) {
                total += 1L;
                continue;
            }
            total += new BigInteger(moved)
                    .subtract(new BigInteger(recorded)).abs().longValue();
        }
        return total;
    }

    private Valuation valuation(int ordinal, Map<String, String> assignment,
                                Map<String, String> moved) {
        List<String> assertions = new ArrayList<String>();
        for (Map.Entry<String, String> entry : assignment.entrySet()) {
            RootMintRow row = corpus.anyRoot(entry.getKey());
            if (row == null) continue;
            String literal = smtLiteral(entry.getValue(), sortOf(row));
            if (literal.isEmpty()) continue;
            assertions.add("(assert (! (= " + row.symbol() + " " + literal
                    + ") :named " + VALUATION_PIN + smtName(row.symbol())
                    + "))");
        }
        return new Valuation(ordinal, assignment, moved, assertions);
    }

    private List<String> alternativesOf(RootDomain domain) {
        List<String> values = new ArrayList<String>();
        String recorded = domain.recordedValue() == null ? ""
                : domain.recordedValue().trim();
        if (domain.kind() == RootKind.MARKER) {
            if ("true".equals(recorded)) values.add("false");
            else if ("false".equals(recorded)) values.add("true");
            return values;
        }
        if (domain.pinned()) return values;
        String min = domain.min();
        String max = domain.max();
        if (min == null || max == null || integralLiteral(min).isEmpty()
                || integralLiteral(max).isEmpty()) {
            return values;
        }
        BigInteger low = new BigInteger(min.trim());
        BigInteger high = new BigInteger(max.trim());
        BigInteger centre = integralLiteral(recorded).isEmpty()
                ? low : new BigInteger(recorded);
        if (centre.compareTo(low) < 0 || centre.compareTo(high) > 0) {
            centre = centre.compareTo(low) < 0 ? low : high;
            values.add(centre.toString());
        }
        List<BigInteger> ends = new ArrayList<BigInteger>(anchors(domain));
        final BigInteger from = centre;
        ends.sort(Comparator.comparing((BigInteger end) ->
                end.subtract(from).abs()).thenComparing(end -> end));
        for (BigInteger end : ends) {
            if (!end.toString().equals(recorded)
                    && !values.contains(end.toString())
                    && values.size() < maxValuations) {
                values.add(end.toString());
            }
        }
        for (BigInteger step = BigInteger.ONE;
             values.size() < maxValuations
                     && (centre.subtract(step).compareTo(low) >= 0
                     || centre.add(step).compareTo(high) <= 0);
             step = step.add(BigInteger.ONE)) {
            for (BigInteger value : new BigInteger[]{
                    centre.subtract(step), centre.add(step)}) {
                if (value.compareTo(low) >= 0 && value.compareTo(high) <= 0
                        && !values.contains(value.toString())
                        && values.size() < maxValuations) {
                    values.add(value.toString());
                }
            }
        }
        return values;
    }


    private boolean unknown(String term, List<GapRow> refusals,
                            String subject) {
        List<String> free = new ArrayList<String>();
        Set<String> bound = SmtNames.letBound(term);
        for (String token : SmtNames.names(term)) {
            if (SmtNames.BUILTIN.contains(token)) continue;
            if (bound.contains(token)) continue;
            if (lowering.defined(token)) continue;
            if (lowering.declareStated(token)) continue;
            free.add(token);
        }
        if (free.isEmpty()) return false;
        refusals.add(GapRow.of(COMPOSITION, GapKind.UNSTATED_VALUE,
                GapClass.DIAGNOSTIC, subject,
                "this term names symbols nothing declares: " + free));
        return true;
    }

    static final String LOOP_BODY_BOUND = "loop-body-bound";

    static final String DAEMON_TICK_BOUND = "daemon-tick-bound";

    static final String COMPOSITION = "composition";

    static final String REFUTED_CLAIM = "refuted_claim__";

    static boolean excludesAModel(String name) {
        return name != null && name.startsWith(REFUTED_CLAIM);
    }

    String leftPath(Arms.Arm arm) {
        PathEnd end = pathEnd;
        return end == null ? null : end.left(corpus, anchor, arm);
    }

    private PathEnd pathEnd;

    static final class PathEnd {
        final String session;
        final long cutoff;
        final Map<String, Boolean> taken = new HashMap<String, Boolean>();
        final Set<String> fatal = new LinkedHashSet<String>();

        PathEnd(String session, List<DecisionRow> decisions, long cutoff) {
            this.session = session;
            this.cutoff = cutoff;
            for (DecisionRow decision : decisions) {
                if (decision.seq() > cutoff) continue;
                taken.put(key(decision), decision.outcome());
                if (decision.seq() == cutoff) fatal.add(key(decision));
            }
        }

        static String key(DecisionRow decision) {
            return decision.siteId() + "#" + decision.ordinal();
        }

        String left(Corpus corpus, OccurrenceAddress anchor, Arms.Arm arm) {
            if (arm.producer() == null
                    || !anchor.id().equals(arm.producer().id())) {
                return null;
            }
            long delivered = arm.deliveredAt();
            if (arm.sessionId().equals(session)) {
                return cutoff != Long.MAX_VALUE && delivered > cutoff
                        ? "delivered by the anchor occurrence after the"
                        + " path's fatal decision (seq " + cutoff + "),"
                        + " where the path throws: no producer for this path"
                        : null;
            }
            Corpus.RecordedPath ran = corpus.path(arm.sessionId(), anchor);
            if (ran == null) return null;
            DecisionRow last = null;
            for (DecisionRow decision : ran.decisions) {
                if (decision.seq() >= delivered
                        || !taken.containsKey(key(decision))
                        || last != null && last.seq() > decision.seq()) {
                    continue;
                }
                last = decision;
            }
            if (last == null) return null;
            String at = key(last);
            if (fatal.contains(at)) {
                return "delivered by the anchor occurrence after its"
                        + " decision at " + at + ", the path's fatal"
                        + " decision, past which the path throws: no"
                        + " producer for this path";
            }
            if (taken.get(at) != last.outcome()) {
                return "delivered by the anchor occurrence after it left"
                        + " this path at " + at + " (" + last.outcome()
                        + " where the path took " + taken.get(at) + "; the"
                        + " path throws at its fatal decision): no producer"
                        + " for this path";
            }
            return null;
        }
    }

    void gap(GapKind kind, GapClass cls, String subject,
                     String detail) {
        gaps.add(GapRow.of(COMPOSITION, kind, cls,
                subject == null || subject.trim().isEmpty()
                        ? anchor.render() : subject, detail));
    }
}
