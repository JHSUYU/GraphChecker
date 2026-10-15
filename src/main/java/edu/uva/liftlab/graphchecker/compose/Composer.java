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
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.smtLiteral;
import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.smtName;
import static edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.integralLiteral;

/**
 * One composed query per anchor, factorized per path.  A MERGE, not a
 * reconstruction: every value was propagated inside some replay; nothing
 * here finds writers, links arms by request family, or picks versions.  It
 * ALIGNs the anchor across sessions, MERGEs one disjunct per admitted path,
 * LOWERs through {@link SmtLowering} and GATEs (fail closed).
 *
 * <p>The shape, for anchor A:</p>
 * <pre>
 *   exactly-one(selector_p)                       over admitted paths p
 *   selector_p =&gt; pi_p /\ phi_p /\ reads_p /\ joins_p /\ valuation_p
 *   selector_p =&gt; family(I)   for every interaction I that p's chain reaches
 *   root domains, clock floors, identity axioms
 * </pre>
 *
 * <p>Deliberately NOT global: a path's arrivals, clock readings and
 * valuation are per session (CONTRACT-SPEC §5); a family sits under its
 * session's
 * selector, so an arm-less family kills only its disjunct; an arm is
 * guarded by its replay's valuation of only the roots its expression
 * depends on (CONTRACT-SPEC §4).</p>
 */
public final class Composer {

    /** One valuation of the declared roots: one question for the solver. */
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

        /** Root id -> the value this valuation gives it. */
        public Map<String, String> assignment() {
            return assignment;
        }

        /** Root id -> its value, for the roots this valuation moved. */
        public Map<String, String> moved() {
            return moved;
        }

        /** The pins, as named assertions the solver conjoins. */
        public List<String> assertions() {
            return assertions;
        }

        @Override
        public String toString() {
            return "valuation " + ordinal
                    + (moved.isEmpty() ? " (recorded)" : " " + moved);
        }
    }

    /** One admitted path, as the composition states it. */
    public static final class Disjunct {
        private final Corpus.RecordedPath path;
        private final String selector;
        /** The name of its {@code (=> selector (and pi ... phi ...))}. */
        private final String fatal;
        /** That implication with phi, the fatal arm, left out: what the
         *  path's own run satisfied ({@link Composition#withoutFatalArm}). */
        private final String withoutFatalArm;
        private final boolean fatalObserved;
        private final Set<String> interactionIds;
        private final Set<String> restsOn;
        /** Where the path decided: its target row's seq, or the way guard's
         *  ({@link PathEntry}). */
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

        /** Every interaction this path's chain reaches. */
        public Set<String> interactionIds() {
            return interactionIds;
        }

        /** The tracked locations its fatal predicate rests on. */
        public Set<String> restsOn() {
            return restsOn;
        }

        /** Where the path decided ({@link PathEntry}). */
        public long cutoff() {
            return cutoff;
        }
    }

    /** What one composition is, before the solver is asked. */
    public static final class Composition {
        /** What the composed paths rest on concretely ({@link Concrete}). */
        private final List<Concrete> concrete;
        /** The declared roots a valuation assigns, and their recordings. */
        private final Map<String, RootMintRow> declaredRoots;
        private final Map<String, String> recordedValues;
        private final OccurrenceAddress anchor;
        private final String body;
        private Cone cone;
        private final List<Disjunct> disjuncts;
        private final List<PathEntry> paths;
        private final List<Family> families;
        private final List<RootDomain> roots;
        /** Each root's category, by root id. */
        private final Map<String, RootCategory> categories;
        /** Each configuration root's reads its plant leaves at the
         *  recording's value (StaticScopeMap#concreteConfigurationReads). */
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
        /** refuted_claim__k -> the model it excludes. */
        private final Map<String, Refutations.Refuted> refutations;
        private final List<JsonObject> refusedPaths;
        private final Map<String, List<String>> ownArms;
        private final Map<String, List<String>> recordedAtPlants;
        private final Map<String, Map<String, List<String>>> worldArms;
        private final String seedSessionId;
        /** The sessions, their worlds and rows ({@link #ranModel}). */
        private final Corpus corpus;
        /** Every CLOCK root this composition anchors -> its reading. */
        private final Map<String, String> clockRootReadings;
        /** Where each top-level command of the body ends, the path
         *  selector it is guarded by (null: every path's; #scopeQuery), and
         *  whether it asserts a refuted claim (#scopeWithoutFatalArm). */
        private final int[] commandEnds;
        private final String[] commandGuards;
        private final boolean[] commandRefuted;
        /** Each command's declared roots ({@link #rootsOf}), read once off
         *  the body when first asked: indices into {@link #rootNames}, null
         *  for a command naming none. */
        private int[][] commandRoots;
        private List<String> rootNames;
        /** Each path's roots ({@link #rootsOf}), by selector. */
        private final Map<String, Set<String>> pathRoots =
                new HashMap<String, Set<String>>();

        /** The composer's state once every path is composed. */
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

        /** Declarations and assertions; no {@code check-sat}. */
        public String body() {
            return body;
        }

        /**
         * One question: the body plus these assertions, written out to its
         * reader, never copied (a body runs past 200 MB and is asked on
         * many threads at once, {@link Disjunction}).  The body is
         * spelled legally once ({@link SmtLowering#body}); the assertions
         * are spelled here, since pins name raw symbols such as
         * {@code CLOCK/...#...} and a bare {@code #} is a bit-vector literal
         * to z3.  Spelling is token-local, so each assertion spelled alone
         * spells the text.
         */
        public ArtifactIO.Body query(List<String> assertions) {
            List<String> legal = legal(assertions);
            return output -> {
                output.write(body);
                for (String assertion : legal) output.write(assertion);
            };
        }

        /**
         * What every path's question shares: the body's commands no path
         * selector guards and that assert no refuted claim, in their order --
         * every declaration and definition among them.  A long-lived z3
         * reads it once ({@code smt.Z3Incremental}); each path's question is
         * then one scope over it ({@link #scopeQuery}).
         */
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

        /**
         * One path's question as a scope over {@link #sharedQuery}: the
         * refuted claims the body asserts, the commands this path's selector
         * guards, the selector asserted, and these assertions.  With the
         * shared part it is the body without the commands another path's
         * selector guards: the partition forces every other selector false,
         * so each command left out held vacuously, and the answer is
         * {@link #query}'s with the selector asserted, but z3 reads what
         * every path shares once and this path's own text, not every
         * path's.  Every command left to a scope is an assertion, read after
         * every declaration as it would be in place.
         */
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

        /**
         * One path's question with its fatal arm left out, as a scope over
         * {@link #sharedQuery}: its {@code path_fatal__} command replaced by
         * the same implication without phi, and no refuted claim asserted (a
         * model CONFIRM refuted is no part of the run itself) -- what its own
         * run satisfied, every root free.  Unsat, the composition
         * contradicts the run itself (ClaimPolicy's self-check).
         */
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

        /**
         * Whether the command between these offsets excludes a model CONFIRM
         * refuted or gave no verdict on ({@link Composer#refutations}): its
         * name closes it, so only its last characters are read.  An
         * unbounded search from there read the rest of the body per command
         * and per path (HR1 hdfs-adhoc-07: 556 sessions, and the self-check
         * of an UNSAT ran past the case's limit).
         */
        private static boolean refutation(String body, int start, int end) {
            String tail = body.substring(Math.max(start, end - 64), end);
            return tail.contains(":named " + REFUTED_CLAIM);
        }

        /**
         * The declared roots (as a valuation pins them, {@link
         * Valuation#assertions}) one path's question names: those its own
         * commands name, closed over the commands every path shares that
         * name one of them and another.  A pin of any other root asserts a
         * value nothing of this path reads ({@code Disjunction}: a path is
         * asked under the pins of these first, and unsat there under every
         * valuation agreeing on them).  Read off the body once for every
         * path; whatever it leaves out only makes that first question
         * weaker, never an unsat it would not be.
         */
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

        /** Each command's declared roots, read off the body once. */
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

        /** The indices gathered for one command, emptied for the next; null
         *  where none. */
        private static int[] indices(Set<Integer> here) {
            if (here.isEmpty()) return null;
            int[] indices = new int[here.size()];
            int at = 0;
            for (int index : here) indices[at++] = index;
            here.clear();
            return indices;
        }

        /** A character of an SMT-LIB simple symbol ({@code
         *  SmtNames#legalSymbols} bar-quotes any other). */
        private static boolean simpleSymbolChar(char c) {
            return Character.isLetterOrDigit(c) || "~!@$%^&*_-+=<>.?/"
                    .indexOf(c) >= 0;
        }

        /** Each assertion spelled legally, one per line. */
        private static List<String> legal(List<String> assertions) {
            List<String> legal = new ArrayList<String>();
            if (assertions == null) return legal;
            for (String assertion : assertions) {
                if (assertion == null || assertion.isEmpty()) continue;
                legal.add(SmtNames.legalSymbols(assertion) + "\n");
            }
            return legal;
        }

        /**
         * The body's top-level commands: where each ends (the first one's
         * text starts at 0, each next at the previous end), and the selector
         * among these that guards it, {@code (assert (=> selector ...))}
         * named or not, else null.  Bar-quoted symbols, string literals and
         * comments are skipped whole, so a parenthesis inside one is none.
         */
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
                            // "" is an escaped quote inside the literal.
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

        /** How much of a command's head names its guard: the assert and
         *  implication heads and a selector, whose names are short. */
        private static final int GUARD_PREFIX = 256;

        /** The selector this command's head is guarded by, or null. */
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

        /** What the composed paths rest on concretely: information, never
         *  a gap (result.json {@code concrete[]}). */
        public List<Concrete> concrete() {
            return concrete;
        }

        /**
         * THE OPEN LINKS of the paths a verdict rests on: each value a path's
         * fatal condition rests on that no producer the corpus attests made
         * -- the set {@code experiments/accept/cone.py} reads off this
         * formula ({@link Cone}) -- each with the producer occurrence its
         * arrival names where no attested export delivered it, the one GROW
         * can plan (PIPELINE §7.9); none where nothing could (a value whose
         * attested producer's export did not lower, an attach naming no
         * producer).  A SAT is judged on the path it claims ({@code
         * witness}, with the arms it chose), an UNSAT on every path it rests
         * on ({@code witness} null).
         */
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

        /** The open links of the paths a SAT does not take: information
         *  ({@code cone.py}'s {@code unboundOffWitness}), never gating. */
        public List<JsonObject> offWitness(ClaimPolicy.Outcome witness) {
            List<JsonObject> open = new ArrayList<JsonObject>();
            for (Disjunct path : disjuncts) {
                if (witness != null && path == witness.selected()) continue;
                links(path, Collections.<String>emptySet(), open);
            }
            return open;
        }

        /** The body's {@link Cone}, read once for all its paths. */
        private synchronized Cone cone() {
            if (cone == null) cone = new Cone(body);
            return cone;
        }

        private void links(Disjunct path, Set<String> arms,
                           List<JsonObject> open) {
            for (String symbol : cone().unbound(path.selector(),
                    path.path().pathId, arms, concrete)) {
                // By the body's spelling, whichever the formula's text
                // names it by (a raw M_L'String'_... and its bar-quoted
                // form are one symbol).
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

        /** Where a moved root's value enters the world: a clock cell's
         *  CLOCK, else its mint's category; null for a key no mint names. */
        public RootCategory categoryOf(String moved) {
            return clockCells.contains(moved) ? RootCategory.CLOCK
                    : categories.get(moved);
        }

        /** Whether these moves move configuration only
         *  ({@link Composer#configurationOnly}): the claim states it. */
        public boolean configurationOnly(Collection<String> moved) {
            return Composer.configurationOnly(moved, this::categoryOf);
        }

        /** Each moved configuration root whose plant leaves reads of its
         *  key at the recording's value, with those reads: a world moving
         *  it is no configuration a cluster could hold. */
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

        /** Every clock cell the formula declares, in the recording's seq
         *  order, each with a reading ({@link #clockReadings}). */
        public List<String> clockCells() {
            return clockCells;
        }

        /** The symbol of every declared root a valuation assigns, as a
         *  query spells it: what a model of the formula is read back for. */
        public List<String> rootSymbols() {
            List<String> symbols = new ArrayList<String>();
            for (RootMintRow row : declaredRoots.values()) {
                symbols.add(SmtNames.legalSymbols(row.symbol()));
            }
            return symbols;
        }

        /**
         * THE FORMULA ITSELF: no root held, each free over its domain, as
         * the body states it -- the question whose answer is the verdict
         * ({@code ClaimPolicy#closed}), asked under this valuation of no
         * pin, numbered {@code ordinal}.
         */
        public Valuation free(int ordinal) {
            return new Valuation(ordinal, recordedValues,
                    Collections.<String, String>emptyMap(),
                    Collections.<String>emptyList());
        }

        /**
         * The valuation a model of the formula assigns (symbol -> value,
         * {@link #rootSymbols}), numbered {@code ordinal}: each declared
         * root at the model's value, moved where that is not its
         * recording's, pinned there as an enumerated valuation is.
         */
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

        /** A model's value as a recording spells it: {@code (- 5)} is -5;
         *  "" for none. */
        private static String modelValue(String model) {
            if (model == null) return "";
            String text = model.trim();
            if (text.startsWith("(-") && text.endsWith(")")) {
                return "-" + text.substring(2, text.length() - 1).trim();
            }
            return text;
        }

        /** Clock cell -> its instant on the recording's timeline: the
         *  seed's reading, or where a session that read it places it
         *  ({@code Composer#clocks}). */
        public Map<String, Long> clockReadings() {
            return clockReadings;
        }

        /** Clock cell -> its clock's tick in nanoseconds
         *  ({@code RootMintRow#clockNanos}). */
        public Map<String, Long> clockNanos() {
            return clockNanos;
        }

        /** Clock cell -> the cell before it on its node's clock, where its
         *  order names one ({@code clock_order__}). */
        public Map<String, String> clockBefore() {
            return clockBefore;
        }

        /** Interaction -> the declared roots its unattested arms mention. */
        public Map<String, Set<String>> unattestedRoots() {
            return unattestedRoots;
        }

        /**
         * Path id -> the interleaving that path's anchor reads actually
         * took: each STATE family's arm the run took
         * ({@link ComposedFamilies#stateFamilies}).
         */
        /**
         * The path's own run: the arm its own session is of each message the
         * path received, and the writer arm each state read observed --
         * selectors, never the values the run's handoffs carried, which are
         * on its own clock ({@code SmtLowering#clockBases}).
         */
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

        /**
         * The arms {@code taken} under the path {@code selector} names that
         * are no pairing its own run had ({@link #ownRun}: its own
         * session's message arms, the writer arm each state read observed,
         * and at a location its world planted a pairing on any arm but the
         * plant, {@code ComposedFamilies#recordedAtPlants}): the re-paired
         * ones, which a pairing kind moved where no root did.  Only that
         * path's: another path's arms are free in the model, as its
         * selector is.  And each pairing the path's session's world planted
         * and its read took ({@link #takenPairings}) at a location no family
         * of the path states (its read had no other writer to be re-paired
         * with), spelled {@code PAIRING:<reader>=<writer>}: the world's
         * pairing is re-paired from the recording's all the same.
         */
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

        /**
         * {@code selected}'s path as its session ran it, plants and all: its
         * own run ({@link #ownRun}) but, at each location its world planted
         * a pairing on, the plant ({@link #worldPlants}) in place of the
         * recording's pairing there (any arm but the plant, which #ownRun
         * holds so {@link #repaired} can tell a re-pairing).
         */
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

        /**
         * {@code selected}'s families held to its world's plants: at each
         * location its session's world planted a pairing on, the plant's
         * arm or the observed arm holding the reads to what it gave them
         * ({@code ComposedFamilies#worldArms}).  What a witness claiming the
         * world's pairing is asked under ({@code ClaimPolicy}).
         */
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

        /**
         * The pairings {@code selected}'s session's world planted (reader ->
         * writer, as {@code runtime.Confirmation} names them) that its read
         * took: the reader's read observed a version the planted writer
         * wrote ({@code Confirmation#writer}), and could have seen another
         * writer ({@link Composer#anotherWriter}, the test that admits a
         * planted read to a family), each with that read.  A plant the
         * replay could not make (an inherited one whose writer came first)
         * is none, and so is one no other writer could have replaced (a
         * write no read could have preceded: the run's).
         */
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

        /**
         * The pairings {@code selected}'s session's world planted that its
         * replay realized: the reader's read observed a version the planted
         * writer wrote ({@code Confirmation#writer}), whether or not another
         * writer could have replaced it, inherited ones too -- what the
         * session ran ({@link #ranWorld}).
         */
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

        /**
         * Path id -> the values that path's ANCHOR's attaches actually
         * received: the wire slots a MESSAGE_PAIRING_FLIPPED witness replaces.
         */
        public List<String> observedArrivals(String pathId) {
            return asserted(observedArrivals.get(pathId));
        }

        /**
         * Every path held, under its selector, to the pairing its own run
         * had (observed reads and received arrivals).  Part of "the run as
         * it happened": without it a healthy path can reach the fatal arm at
         * the recorded valuation through a delivery its run never took.
         */
        public List<String> recordedPairings() {
            List<String> held = new ArrayList<String>();
            for (Disjunct disjunct : disjuncts) {
                List<String> terms = new ArrayList<String>();
                List<String> reads = observedReads.get(disjunct.path().pathId);
                List<String> arrivals =
                        heldArrivals.get(disjunct.path().pathId);
                if (reads != null) terms.addAll(reads);
                if (arrivals != null) terms.addAll(arrivals);
                if (terms.isEmpty()) continue;
                held.add("(assert (=> " + disjunct.selector() + " "
                        + VmTermLowering.and(terms) + "))");
            }
            return held;
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

        /**
         * Whether {@code selected}'s session is itself the run of a model
         * moving {@code movedRoots} (a claim's: a root id, or a clock cell
         * at the model's instant): it ran the model's world ({@link
         * Moved#ranBy}, the test CONFIRM's realizedBy applies to a claim).
         */
        public boolean ranModel(Disjunct selected,
                                Map<String, String> movedRoots) {
            return ran(selected, movedRoots, true);
        }

        /** {@link #ranModel} but its clocks ({@link Moved#ranRootsBy}). */
        public boolean ranRoots(Disjunct selected,
                                Map<String, String> movedRoots) {
            return ran(selected, movedRoots, false);
        }

        /**
         * Whether {@code selected}'s session is itself the run of a world
         * pairing's claim: the model's moves ({@link #ranModel}'s test) and
         * exactly the pairings {@code readers} took ({@link
         * Moved#ranWorldBy}).
         */
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

        /** How a pairing's read lies on a path's fatal path ({@link
         *  #onFatalPath}). */
        public enum FatalPath {
            /** Its symbol is in the path's cone. */
            CONE,
            /** A read no term names, made by the anchor's occurrence. */
            ANCHOR,
            /** A read no term names, whose occurrence -- or one it is the
             *  role prefix of ({@link Corpus#rolePrefix}) -- wrote a version
             *  a read in the cone, or a read of the anchor's occurrence,
             *  observed. */
            WROTE
        }

        /**
         * How a pairing's read lies on {@code selected}'s fatal path (a world
         * pairing's claim, {@code ClaimPolicy}): its symbol in the path's
         * cone ({@link #cone}); or -- a read no term names: a key an older
         * document lacks decides nothing the VM states -- its occurrence is
         * the anchor's, or wrote a version a read in the cone, or a read
         * the anchor's own occurrence made, observed (a store version the
         * stale view's work wrote back, a field the anchor reads; the
         * occurrence-level reading ANCHOR takes), a role read counting as
         * the read of each occurrence it is the role prefix of, by the rule
         * a pairing flip is offered by ({@link Corpus#rolePrefix}: round SG3B
         * tra, node1's getAliases() view read in the request's role work,
         * whose alias update wrote {@code /aliases.json} v3, which the
         * client's request read while its retry timer -- the fatal term,
         * naming no read -- ran out).  CONFIRM stays the strict filter: it
         * plants the pairing and must reach the fatal.  Null where none
         * holds.
         */
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

        /** Session -> location@version -> its reads of it. */
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

        /** Whether the cone names {@code symbol}, as written or quoted. */
        private static boolean named(Set<String> cone, String symbol) {
            return symbol != null && (cone.contains(symbol)
                    || cone.contains(SmtNames.legalSymbols(symbol)));
        }

        /**
         * The valuation {@code selected}'s session's world planted, numbered
         * {@code ordinal}: each declared root at the world's value, else its
         * recording's, pinned as {@link #modelValuation} pins.
         */
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

        /**
         * {@code selected}'s session's world's clocks as named pins: a cell
         * whose CLOCK root the world skewed at that skew off its root's
         * reading ({@link Moved}'s timeline), every other cell running on
         * from the cell before it ({@link #clockStep} at 0).
         */
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

        /** The admitted paths the composition refused by name, each with
         *  its first refusal: no disjunct of the formula, so an UNSAT says
         *  nothing about them ({@code refusedPaths}). */
        public List<JsonObject> refusedPaths() {
            return refusedPaths;
        }

        /** Whether this formula excludes a model CONFIRM refuted ({@link
         *  Composer#refutations}): an UNSAT may then rest on one, which only
         *  an unsat core shows. */
        public boolean assertsRefutations() {
            return !refutations.isEmpty();
        }

        /**
         * The exclusions an unsat core names (its {@code refuted_claim__k}
         * labels), each as the model it
         * excludes: what an UNSAT rests on beside the corpus ({@code
         * restsOnRefutations}).
         */
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

        /**
         * Every family ARM selector, so a claim can say which delivery of a
         * slot the witness model used.
         */
        public List<String> armSelectors() {
            return new ArrayList<String>(armChoices.keySet());
        }

        /**
         * Whether a family offers the path {@code selector} names an arm to
         * choose: where none does, the path's own run is the only one the
         * formula asks of it ({@code ClaimPolicy#worldPairing}).
         */
        public boolean offersArms(String selector) {
            String ordinal = Refutations.ordinal(selector);
            for (String arm : armChoices.keySet()) {
                if (Refutations.ordinal(arm).equals(ordinal)) return true;
            }
            return false;
        }

        /** The delivery one arm selector stands for, or null. */
        public ComposedFamilies.ArmChoice arm(String selector) {
            return armChoices.get(selector);
        }

        /**
         * Every nested selector a state arm's stores are chosen among
         * ({@link ComposedFamilies.ArmChoice#states}), so a claim can say
         * which state of the delivered object the witness's queries saw.
         */
        public List<String> stateSelectors() {
            Set<String> selectors = new LinkedHashSet<String>();
            for (ComposedFamilies.ArmChoice arm : armChoices.values()) {
                for (SmtLowering.StateChoice state : arm.states()) {
                    selectors.add(state.selector);
                }
            }
            return new ArrayList<String>(selectors);
        }

        /**
         * The symbol of every leaf an arm binds that CONFIRM holds a run to
         * ({@link ComposedFamilies.BoundLeaf#held}: a delivery into the
         * anchor), so a claim can state the model's
         * valuation of each ({@link ComposedFamilies#texts}).
         */
        public List<String> heldSymbols() {
            Set<String> symbols = new LinkedHashSet<String>();
            for (ComposedFamilies.ArmChoice arm : armChoices.values()) {
                for (ComposedFamilies.BoundLeaf leaf : arm.leaves().values()) {
                    if (leaf.held(anchor.id())) symbols.add(leaf.symbol);
                }
            }
            return new ArrayList<String>(symbols);
        }

        /**
         * The causal cone of one path's fatal, as acceptance reads it off
         * the formula ({@code experiments/accept/cone.py}): every name its
         * {@code path_fatal__} names, closed over the message families
         * asserted under its selector that name one of them.
         */
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

        /** Selector -> its cone ({@link #cone}): the body never changes. */
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

        /** Every selector, for reading which disjunct a model selected. */
        public List<String> selectors() {
            return Composer.selectors(disjuncts);
        }

        /** The disjunct one selector names, or null. */
        public Disjunct bySelector(String selector) {
            for (Disjunct disjunct : disjuncts) {
                if (disjunct.selector().equals(selector)) return disjunct;
            }
            return null;
        }
    }

    private final Corpus corpus;
    private final OccurrenceAddress anchor;
    /** The epoch's static facts: where a reference write's construction
     *  guard is ({@link #constructionGuards}). */
    private final StaticScopeMap scope;
    private final int maxValuations;
    private final SmtLowering lowering;
    private final List<GapRow> gaps = new ArrayList<GapRow>();
    /** Each store content leaf an unattested producer settles, by its
     *  symbol ({@link #arrival}): named per producer at the end, counted
     *  over the paths kept ({@link #compose}). */
    private final Map<String, Refused> settledLeaves =
            new LinkedHashMap<String, Refused>();
    private final Map<String, Family> families =
            new LinkedHashMap<String, Family>();
    /** Root id -> the domain the case and the recording give it. */
    /** The declared roots the enumeration moves (rootId -> its row), set
     *  by {@link #valuations}: what a model of the formula assigns. */
    private final Map<String, RootMintRow> declaredRoots =
            new LinkedHashMap<String, RootMintRow>();
    private final Map<String, RootDomain> roots =
            new LinkedHashMap<String, RootDomain>();
    /** The one family-arm rule, shared with the flip solver. */
    private final Arms arms;
    /**
     * Interaction -> the declared roots an UNATTESTED arm of it mentions.
     * Such an arm has no producer path condition, so a witness may not move
     * a root inside it (IDENTITY §4).
     */
    private final Map<String, Set<String>> unattestedRoots =
            new LinkedHashMap<String, Set<String>>();
    /** Path id -> the family arms its anchor reads took. */
    private final Map<String, List<String>> observedReads =
            new LinkedHashMap<String, List<String>>();
    /**
     * Path id -> what every attach a family binds received, anchor and
     * upstream ({@link Composition#recordedPairings}).  Not what a mechanism
     * is named by: upstream arrivals are consequences of roots and clocks.
     */
    private final Map<String, List<String>> heldArrivals =
            new LinkedHashMap<String, List<String>>();
    /** Path id -> what the anchor's attaches received. */
    private final Map<String, List<String>> observedArrivals =
            new LinkedHashMap<String, List<String>>();
    /** Each arrival no producer's export binds -- none the corpus attests,
     *  or an attested one whose exports do not lower -- by the symbol as the
     *  body spells it: the producer its attach names, or null
     *  (Composer#arrival, Composition#openChain). */
    private final Map<String, Endpoint> openArrivals =
            new LinkedHashMap<String, Endpoint>();
    /** This epoch's skeleton: which interactions have a slot (PIPELINE
     *  §7.1). */
    private SlotTable slots;
    /** Sessions whose pairing replaces a slot's: their arms are not ours. */
    private final Set<String> replacing = new LinkedHashSet<String>();
    /** What refused the first path that reached the anchor, or "". */
    private String firstRefusal = "";
    /** The admitted paths refused by name ({@link #refused}). */
    private final List<JsonObject> refusedPaths = new ArrayList<JsonObject>();
    /** Every CLOCK root's reading on the recording's timeline, by root id
     *  ({@link #placeClocks}). */
    private final Map<String, Long> clockTimeline =
            new LinkedHashMap<String, Long>();
    /** Each symbol of a CLOCK root no session can place on that timeline,
     *  with its root id ({@link #placeClocks}, {@link #unplacedClocks}). */
    private final Map<String, String> unplacedClocks =
            new LinkedHashMap<String, String>();
    /** Each refuted claim this formula excludes, by its assertion's name
     *  ({@link #refutations}). */
    private final Map<String, Refutations.Refuted> refutationNames =
            new LinkedHashMap<String, Refutations.Refuted>();
    /** What the path being composed rests on concretely or leaves free
     *  ({@link Concrete}), kept once the path is a disjunct. */
    private final Map<String, Concrete> pathConcrete =
            new LinkedHashMap<String, Concrete>();
    /** What the composed paths rest on concretely, by subject. */
    private final Map<String, Concrete> concrete =
            new LinkedHashMap<String, Concrete>();
    /** How the alternatives of one slot read in SMT. */
    private final ComposedFamilies composedFamilies;
    /** What a path or an arm rests on ({@link RestsOn}). */
    final RestsOn restsOn;

    private Composer(Corpus corpus, OccurrenceAddress anchor,
                     int maxValuations, StaticScopeMap scope) {
        this.corpus = corpus;
        this.anchor = anchor;
        this.scope = scope;
        this.restsOn = new RestsOn(corpus, scope, anchor);
        this.maxValuations = maxValuations <= 0 ? 64 : maxValuations;
        this.lowering = new SmtLowering(corpus.declaredSymbols());
        lowering.clockBases(clockBases());
        this.arms = new Arms(corpus);
        this.composedFamilies = new ComposedFamilies(this, corpus, arms,
                lowering, families, unattestedRoots, replacing, gaps);
    }

    /** This epoch's skeleton, for the relocated family bodies. */
    SlotTable slots() {
        return slots;
    }

    /** Composes the declared occurrence; a missing one is a claim, not a
     *  crash.  Each root's domain is the corpus's ({@link
     *  Corpus#domainOf}). */
    public static Composition compose(Corpus corpus,
                                      OccurrenceAddress anchor,
                                      int maxValuations,
                                      StaticScopeMap scope) {
        return new Composer(corpus, anchor, maxValuations, scope).run();
    }

    /** Every how many admitted paths the composer says how far it is. */
    private static final int PROGRESS_PATHS = 25;

    private Composition run() {
        // One symbol for two roots makes paths unsat; refuse it.
        for (Map.Entry<String, Set<String>> collision
                : corpus.collidingRootSymbols().entrySet()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING,
                    collision.getKey(), "one solver name for "
                            + collision.getValue().size() + " roots: "
                            + collision.getValue());
        }

        // A session read short would hide missing decisions.
        for (SessionReader session : corpus.sessions()) {
            if (session.incomplete().isEmpty()) continue;
            gap(GapKind.SESSION_INCOMPLETE, GapClass.BLOCKING,
                    session.sessionId(), "this session could not be read "
                            + "whole: " + session.incomplete());
        }

        // A verdict is the session's own row; the wave's aggregate copy (the
        // row of the worker that landed this session) is checked against it,
        // and a disagreement is BLOCKING.
        for (SessionReader session : corpus.sessions()) {
            for (ObligationResult settled : session.obligations()) {
                ObligationResult wave = corpus.waveVerdict(
                        session.sessionId(), settled.obligationId());
                if (wave == null || wave.verdict() == settled.verdict()) {
                    continue;
                }
                gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING,
                        settled.obligationId(), "the replay that ran this "
                                + "obligation states " + settled.verdict()
                                + " in session " + session.sessionId()
                                + " and the wave's own file states "
                                + wave.verdict() + ", so what it settled is "
                                + "stated twice and differently");
            }
        }

        // Exactly one session must STATE role SEED (manifest.json); never
        // infer it from "focused nothing".
        List<String> seeds = corpus.seedSessionIds();
        if (seeds.size() != 1 && !corpus.sessions().isEmpty()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING, seeds.toString(),
                    seeds.isEmpty()
                            ? "no session of this corpus states role SEED, "
                            + "so none of them is the recording"
                            : seeds.size() + " sessions of this corpus state "
                            + "role SEED, so which one is the recording has "
                            + "no answer");
        }

        // The skeleton first: a replacing session's rows must not reach a
        // family.
        try {
            slots = SlotTable.read(corpus.iteration());
        } catch (java.io.IOException | RuntimeException unreadable) {
            // Unreadable skeleton: named, and composition fails closed.
            slots = null;
            gap(GapKind.TOPOLOGY_DIVERGENCE, GapClass.BLOCKING,
                    SlotTable.FILE, "this epoch's slot table could not be "
                            + "read: " + unreadable);
        }
        if (slots != null) {
            for (SlotTable.Replacement replacement
                    : slots.replacements(corpus)) {
                // FAIL CLOSED ON THE ARMS, OPEN ON THE CLAIM: its arms never
                // reach a family, but only an ADMITTED replay's replacement
                // blocks ({@link SessionReader#admitted}).
                replacing.add(replacement.sessionId);
                gaps.add(GapRow.of(replacement.sessionId,
                        GapKind.TOPOLOGY_DIVERGENCE, replacement.cls(),
                        replacement.consumerEndpointId,
                        replacement.detail()));
            }
        }

        placeClocks();
        List<Disjunct> disjuncts = new ArrayList<Disjunct>();
        List<PathEntry> entries = new ArrayList<PathEntry>();
        List<Corpus.RecordedPath> admitted = restsOn.admitted(gaps);
        int ordinal = 0;
        int done = 0;
        long started = System.nanoTime();
        for (Corpus.RecordedPath path : admitted) {
            Disjunct disjunct = compose(path, ordinal);
            if (disjunct != null) {
                disjuncts.add(disjunct);
                entries.add(PathEntry.of(path.pathId, path.sessionId,
                        disjunct.selector(), disjunct.fatalObserved(),
                        disjunct.restsOn(), disjunct.cutoff()));
                ordinal++;
            }
            if (++done % PROGRESS_PATHS == 0 || done == admitted.size()) {
                System.err.println("compose: path " + done + " of "
                        + admitted.size() + " (" + ordinal + " composed) in "
                        + TimeUnit.NANOSECONDS.toSeconds(System.nanoTime()
                        - started) + " s");
            }
        }
        if (disjuncts.isEmpty()) {
            // Say which absence: no admitted path, or all were refused.
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
            // OR over selectors = OR_p (pi_p and phi_p), since each path
            // asserts selector => its conjunction.
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
        lowering.assertIdentitiesDistinct();
        // Corpus inconsistencies (one name, two sorts; one truncated name,
        // two identities) are BLOCKING gaps, not exceptions.
        for (Map.Entry<String, String> conflict
                : lowering.sortConflicts().entrySet()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING,
                    conflict.getKey(), "this corpus states one solver name "
                            + "at two sorts: " + conflict.getValue());
        }
        for (Map.Entry<String, String> collision
                : lowering.nameCollisions().entrySet()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING,
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
        // Every store content leaf an unattested producer settles on a
        // path kept, named per producer, rule and kind (#arrival): never
        // silent.  One held past the daemon tick bound is that bound, by
        // name (run_engine.sh campaign_bounds: daemon_tick_bound).
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

        // Valuations before the body: the body declares what pins reach.
        List<Valuation> valuations = valuations();
        List<String> pins = new ArrayList<String>();
        for (Valuation valuation : valuations) {
            pins.addAll(valuation.assertions());
        }
        return new Composition(this, lowering.body(pins), disjuncts, entries,
                valuations, clockCells, clockReadings, clockNanos,
                clockBefore);
    }

    // ------------------------------------------------------------------
    // Admission.
    // ------------------------------------------------------------------

    // ------------------------------------------------------------------
    // One path.
    // ------------------------------------------------------------------

    private Disjunct compose(Corpus.RecordedPath path, int ordinal) {
        String session = path.sessionId;
        TargetRow target = corpus.target(session, anchor);
        if (target == null) return null;
        String selector = "path_selector__" + ordinal + "__"
                + ArtifactIO.digest(path.pathId, 10);
        lowering.declare(selector, Sort.BOOL);
        lowering.path();
        // Where the path decided, and its fatal arm (RestsOn#decided).
        RestsOn.Decided decided = restsOn.decided(session, target,
                path.decisions);
        DecisionRow way = decided.way;
        boolean symbolicWay = decided.symbolicWay;
        long cutoff = decided.cutoff;
        String fatalTerm = decided.fatalTerm;
        pathEnd = new PathEnd(session, path.decisions, cutoff);
        // (0a) THE CLOSURE (P3): the occurrences of this session the joins
        //      reach, and the seq each prefix runs to.  Row-level, before
        //      any lowering.
        RestsOn.Reached reached = restsOn.closure(session, anchor, cutoff,
                null);
        // What a family may move is no constant anywhere in this path: not
        // a pin after a refused join, not a variable independence leaves
        // out.  ONE entry point: the anchor's reads and the world's planted
        // ones, less a location a reader mutated a container through.
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

        // (0a') What phi rests on (constraint independence): conditions and
        //       reads sharing no variable with phi or a root stay out.
        List<DecisionRow> conditions = RestsOn.before(path.decisions, cutoff);
        conditions.addAll(restsOn.reachedConditions(session, reached));
        Independence relevant = restsOn.independence(session,
                Collections.singletonList(fatalTerm),
                familyBound(session, repairing.reads), reached,
                conditions);
        //       What the fatal itself rests on ({@link #fatalRests}) and
        //       the roots alone: a location a family binds and nothing else
        //       reaches holds the formula's alternatives, not the witness (a
        //       confirming run is held to these only).
        Set<String> fatalLocations = new LinkedHashSet<String>(
                restsOn.independence(session, fatalRests(fatalTerm,
                        path.decisions, cutoff),
                        Collections.<String>emptySet(), reached, conditions)
                        .locations());
        //       And the store versions its guards read through a decode,
        //       which no term names (RestsOn#storeLocations).
        fatalLocations.addAll(restsOn.storeLocations(session, reached));

        // (0b) Reads whose value the row states outright, bound BEFORE any
        //      lowering so every leaf naming them resolves, not just later
        //      ones.
        Set<String> answered = new LinkedHashSet<String>();
        statedReads(session, reached.keySet(), relevant, rows, refusals,
                joins, answered);

        // (1) The valuation this replay ran under, for every VARIED root
        //     (a root may be written and never branched on) and every root
        //     it read and minted none.  Declared roots this session neither
        //     minted nor read are answered in (1b), once the path's terms are
        //     whole.
        Map<String, Set<String>> unminted =
                new LinkedHashMap<String, Set<String>>();
        terms.addAll(valuationOf(session, refusals, unminted));

        // (2) Each anchor handoff, answered or not: its family binds it
        //     (collected in `bound`), never a literal; one no producer this
        //     corpus attests is held in `holds`.
        Set<String> handoffs = new LinkedHashSet<String>();
        List<String> holds = new ArrayList<String>();
        List<AttachRow> bound = new ArrayList<AttachRow>();
        handoffReads(session, handoffs, holds, bound);

        // (3) State joins, read := observed write's expression, kept by
        //     symbol: a read with family alternatives must not also be
        //     asserted here.
        stateJoins(session, reached.keySet(), relevant, rows, refusals,
                joined, joins, answered);
        joined.removeIf(read -> pinned.contains(
                SmtLowering.locationKey(read.location())));
        //     A field projected, or a container queried, through one a STATE
        //     family may re-point is the object's it is
        //     ({@link SmtLowering#movable}); through any other, the run's.
        for (ReadRow read : joined) {
            if (moved.contains(SmtLowering.readKey(SmtLowering.locationKey(
                    read.location()), read.seq()))) {
                lowering.movable(read);
            }
        }

        // (4) pi_p: decisions STRICTLY BEFORE the target's seq.  The anchor
        //     decision shares the target's seq; including it would
        //     contradict phi on every healthy path.
        terms.addAll(prefix(path.decisions, cutoff, "decision ",
                relevant, refusals));

        // (4b) P3: the prefix of every OTHER occurrence the joins reach,
        //      strictly before the write that reached it: a joined value
        //      without its producer's decisions has no reason (and clock
        //      readings live only there).  Per session, already under this
        //      path's valuation; a handoff producer's prefix is stated inside
        //      its family ({@link #prefix}).
        terms.addAll(closureConditions(session, reached, relevant,
                refusals));

        // (5) phi_p is the FATAL arm as published; never re-derive its
        //     polarity.  A concrete fatal condition is the constant of its
        //     arm (invariant 9): `true` rests the fatal on pi_p, the path
        //     condition that reached the anchor; `false` is the constant
        //     healthy decision, a disjunct no valuation of this formula
        //     satisfies (what was concrete is EXPLORE's concreteAnchors).
        //     A path that left the way to the throw at a guard: at a
        //     SYMBOLIC one, its fatal arm is that guard's other arm, the way
        //     to the throw (a witness turns it, CONFIRM judges the rest);
        //     at a concrete one, the constant false; the guard named in
        //     concrete[] (WAY) with what its term rests on.  One that left
        //     it at no guard stopped on the way (RestsOn#decided): the
        //     constant false, named WAY with how it stopped.  Where a
        //     loop bound cut its occurrence -- before it left the way or
        //     after -- a gap the case's `bounded`
        //     counts (run_engine.sh campaign_bounds: loop_body_bound), so
        //     its UNSAT rests on that bound; a failure of the loop
        //     accounting itself is a BLOCKING defect (RestsOn#cut).  None
        //     stated is no phi.
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
            // The decisions up to the guard (all of them where it left at
            // none named); the guard itself is the fatal arm when symbolic.
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

        // (5b) Every OTHER handoff the conjunction reaches (via joins, pi,
        //      phi), by the same rule as (2).
        List<String> reaching = new ArrayList<String>(terms);
        reaching.addAll(joins.values());
        reaching.addAll(holds);
        reachedHandoffs(session, lowering.reachedSymbols(reaching), handoffs,
                holds, bound, refusals, "");
        terms.addAll(holds);
        //      What the path read only through its view's case of another
        //      version rests on that version's choice (SmtLowering
        //      #viewGuarded): its messages are closed under the choice (6b).
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

        // Read BEFORE end() forgets them: any refusal drops the whole path
        // (it would otherwise rest on a free constant).
        List<String> refused = new ArrayList<String>(
                lowering.openRefusals());
        terms.addAll(lowering.end());

        // (1b) Refuse the path only if its own terms name a declared root
        //      this session never minted ({@link #unstatedRoots}), or a
        //      clock cell with no instant on the recording's timeline
        //      ({@link #unplacedClocks}).
        if (!unminted.isEmpty() || !unplacedClocks.isEmpty()) {
            Set<String> named = named(terms, joins);
            unstatedRoots(session, unminted, named, refusals);
            unplacedClocks(session, named, refusals);
        }
        for (String refusal : refused) {
            refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, refusal,
                    "this path rests on a value the recording does not "
                            + "state, so it is not in the disjunction"));
        }
        if (!refusals.isEmpty()) {
            refused(path, refusals);
            return null;
        }

        // (6) Families: one selector per (producer occurrence, session) for
        //     every interaction reached, under this path's selector.  If no
        //     single session could make all deliveries the path took (PIPELINE
        //     §8), the path is dropped, and what its families stated is taken
        //     back with it.
        List<String> familyTerms = new ArrayList<String>();
        List<GapRow> unproducible = new ArrayList<GapRow>();
        if (!composedFamilies.closeFamilies(ordinal, selector, session,
                interactionIds, bound, familyTerms, unproducible)) {
            composedFamilies.discard();
            refused(path, unproducible);
            return null;
        }
        // (6b) The messages of the versions its view may hold, each under
        //      its version choice; one no session can send -- or with a
        //      leaf no producer the corpus attests made -- is no version the
        //      read is paired to: the path holds its choice false, and its
        //      leaves are no open link (UNPAIRED).
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
        // (7) And the STATE families: which writer the read may have seen.
        //     A read a family gives alternatives to takes its value there.
        Set<String> chosen = composedFamilies.stateFamilies(path,
                ordinal, selector, joined, joins, interactionIds,
                familyTerms, observed, repairing.planted);
        // (8) And the state joins this conjunction ASKS ABOUT.
        terms.addAll(statedJoins(joins, chosen, terms, familyTerms));

        // Nothing refuses the path from here: it is a disjunct.
        composedFamilies.commit();
        String fatal = "path_fatal__" + ordinal;
        List<String> withoutFatalArm = new ArrayList<String>(terms);
        if (fatalArm >= 0) withoutFatalArm.remove(fatalArm);
        // A constant healthy decision is conjoined unflattened, so the body
        // still declares what the rest of the path names: the self-check
        // asks the path without it (Composition#withoutFatalArm).
        String conjunction = fatalArm >= 0
                && "false".equals(terms.get(fatalArm))
                ? "(and " + VmTermLowering.and(withoutFatalArm) + " false)"
                : VmTermLowering.and(terms);
        lowering.assertNamed(fatal,
                "(=> " + selector + " " + conjunction + ")");
        observedReads.put(path.pathId, observed);
        for (SmtLowering.Unbound value : lowering.unbound().subList(
                unboundBefore, lowering.unbound().size())) {
            // One row per value and arm: an arm's own run holds its value;
            // an unpaired version's leaf is dead whatever held it.
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

    /**
     * The versions of a view the path may hold whose content it names has a
     * leaf no producer the corpus attests made (held or free, never bound
     * by a family nor settled by rule): no delivery of that version is a
     * sender the formula may choose, so the version is unpaired, named
     * ({@code ComposedFamilies#closeViewVersions}).
     *
     * @return version choice -> why it is unpaired
     */
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

    /**
     * What the fatal a target row states rests on: its phi; a concrete
     * fatal condition states phi as the constant of its arm, which names
     * nothing, and that fatal rests on the path condition that reached the
     * anchor, the decisions before the target (CONTRACT-SPEC §2.2).
     */
    private static List<String> fatalRests(String fatalTerm,
                                           List<DecisionRow> decisions,
                                           long cutoff) {
        String phi = fatalTerm.trim();
        return "true".equals(phi) || "false".equals(phi)
                ? Arms.pathCondition(decisions, cutoff)
                : Collections.singletonList(fatalTerm);
    }

    /**
     * THE DECISIONS OF A PATH THAT TOOK THE HEALTHY ARM CONCRETELY, stated:
     * each decision up to {@code upTo} (the anchor's own deciding guard
     * included) that pi_p does not state -- independence left it out, none
     * of its variables moving, or it states no term -- is conjoined as a
     * proposition named for it ({@code decided__}) at the arm it took, and
     * named in concrete[] (DECISION) with its term, so the formula states
     * the path the run took and not a bare constant.  Its term is not
     * lowered: over nothing that moves it holds at its recorded value in
     * every world, so it adds no answer, and lowered it can contradict the
     * run where the lowering is less precise than the run (hdfs-adhoc-07:
     * 25 of 33 healthy paths unsatisfiable without their fatal arm).
     */
    private List<String> healthyDecisions(String session, int ordinal,
                                          List<DecisionRow> decisions,
                                          long upTo,
                                          Independence relevant) {
        List<String> stated = new ArrayList<String>();
        for (DecisionRow decision : decisions) {
            // pi_p states a kept decision whose term it can state.
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

    /** Files one admitted path's refusals, the path named with its first
     *  ({@link Composition#refusedPaths}: a dropped path is never silent);
     *  the first of all names an empty disjunction. */
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

    /**
     * The state joins THIS CONJUNCTION ASKS ABOUT, to a fixed point seeded
     * by the path's terms and its family terms.  An unreached join
     * constrains nothing but drags its theory (e.g. {@code assoc_put}) into
     * the query, which can cost z3 its whole budget; it goes with what its
     * lowering required ({@link SmtLowering#ownConditions}).  Same rule as
     * {@link SmtLowering#body}, applied to assertions.
     */
    List<String> statedJoins(Map<String, String> joins,
                                     Set<String> chosen, List<String> terms,
                                     List<String> familyTerms) {
        Map<String, String> pending = new LinkedHashMap<String, String>();
        for (Map.Entry<String, String> join : joins.entrySet()) {
            // A family-chosen read takes its value from the family.
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
        // In row order, so runs compare stably.
        List<String> stated = new ArrayList<String>();
        for (Map.Entry<String, String> join : joins.entrySet()) {
            if (asked.contains(join.getKey())) stated.add(join.getValue());
        }
        return stated;
    }

    /**
     * What this replay ran every varied root at: {@link Corpus#rootValue}
     * (the mint's reading, or the obligation's assignment where the replay
     * PLANTED it; a flip mint states no recorded value) -- and every root it
     * read and minted none, at its reading ({@link Corpus#ranRoot}), by the
     * rule its arms are guarded by ({@code Arms#arm}).
     */
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
                // Read where none was minted: its terms are literals that
                // may be computed from the reading, so the path holds at it
                // alone -- pinned, varied or not, never a window.
                String literal = smtLiteral(corpus.rootValue(session,
                        concrete.rootId()), sortOf(concrete));
                if (literal.isEmpty()) continue;
                lowering.declareStated(concrete.symbol(), sortOf(concrete));
                valuation.add("(= " + concrete.symbol() + " " + literal
                        + ")");
                continue;
            }
            if (row == null) {
                // Not minted here: never pin another session's reading.
                // Collect its symbols; {@link #unstatedRoots} refuses only
                // if this path's own terms name one.  Do not ask
                // `lowering.declared`: the query spans earlier paths.
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
            // Minted but no value stated: the disjunct would decide
            // nothing.  Not gated on the symbol being declared (circular:
            // only this pin declares a marker).
            if (ran.isEmpty() && row.declared()) {
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.BLOCKING, any.rootId(),
                        "this replay minted a declared root and states no "
                                + "value it ran it at: its mint states none "
                                + "and no obligation it ran under assigns "
                                + "it"));
                continue;
            }
            // Mint and obligation disagree: refuse.
            String read = corpus.rootReading(session, row.rootId());
            if (!read.isEmpty() && !read.equals(ran)) {
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.BLOCKING, any.rootId(),
                        "this session's mint states \"" + read + "\" and the "
                                + "obligation it ran under assigns \"" + ran
                                + "\", so what this replay ran the root at "
                                + "is stated twice and differently"));
                continue;
            }
            if (!corpus.varied(row.rootId())) continue;
            lowering.declareStated(row.symbol(), sortOf(row));
            // A declared domain is a window around THIS replay's reading;
            // pinning the exact value would answer the question in advance.
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

    /**
     * The symbols a path's OWN terms (and joins) name: both {@link
     * SmtLowering#reachedSymbols} (leaves, through container bodies) and
     * {@link SmtNames#names} (symbols written into published text), whole
     * tokens only.
     */
    private Set<String> named(List<String> terms, Map<String, String> joins) {
        List<String> texts = new ArrayList<String>(terms);
        texts.addAll(joins.values());
        Set<String> named = lowering.reachedSymbols(texts);
        for (String text : texts) named.addAll(SmtNames.names(text));
        return named;
    }

    /**
     * Refuses the path for each declared root it did not mint whose symbol
     * its own terms name ({@link #named}); otherwise that quantity would be
     * free.  Roots it never names are not refused.
     */
    private void unstatedRoots(String session,
                               Map<String, Set<String>> unminted,
                               Set<String> named,
                               List<GapRow> refusals) {
        for (Map.Entry<String, Set<String>> root : unminted.entrySet()) {
            for (String symbol : root.getValue()) {
                if (!named.contains(symbol)) continue;
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.BLOCKING, root.getKey(),
                        "this path's own terms name this declared root ("
                                + symbol + ") and this session minted no "
                                + "value for it, so what the path rests on "
                                + "is stated by no row of the execution it "
                                + "is about"));
                break;
            }
        }
    }

    /**
     * Refuses the path for each clock cell its own terms name ({@link
     * #named}) that no session can place on the recording's timeline
     * ({@link #placeClocks}): no claim could say whether a witness moved it,
     * so the path is not in the disjunction, named; every other path is.
     */
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

    /** One declared root's window around THIS session's reading, or "". */
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

    /** {@code min <= symbol <= max}: a declared domain as one predicate. */
    private static String window(String symbol, String min, String max) {
        return "(and (>= " + symbol + " " + integralLiteral(min) + ") (<= "
                + symbol + " " + integralLiteral(max) + "))";
    }

    /**
     * Each of the anchor's handoffs, by {@link #arrival}.
     */
    private void handoffReads(String session, Set<String> handoffs,
                              List<String> holds, List<AttachRow> bound) {
        for (AttachRow attach : corpus.attachesOn(session, anchor)) {
            if (handoffs.add(attach.symbol())) {
                arrival(session, attach, holds, bound);
            }
        }
    }

    /**
     * Every OTHER handoff a conjunction names, by {@link #arrival}: a
     * path's (e.g. a delivered value a joined write put into a container)
     * and an arm's alike ({@link ComposedFamilies}: those its delivery and
     * its closure's conditions and joins read).  {@code handoffs} holds the
     * symbols the conjunction states already.  A handoff variable the
     * session minted no attach for (the corpus states it of another run)
     * has no family there, and refuses the conjunction by name.
     *
     * @param arm the arm selector whose conjunction names them, "" for the
     *            path's own
     */
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
                // A leaf an export binds names what that export read: each
                // handoff of it by the same rule.
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

    /**
     * THE ONE RULE for one arrival a conjunction names, a path's and an
     * arm's alike (PIPELINE §8), stated once per conjunction.  An ATTESTED
     * DELIVERY made it -- a run whose own pairing named this consumer ran
     * its producer instrumented ({@link Arms#attestedDeliveries}, the
     * selection the slot's family arms are made by), its session not one a
     * GROW re-run replaces: its FAMILY alone binds it (it joins {@code
     * bound}); nothing is conjoined here, and it takes just its sort from
     * the delivery ({@link #attestedArrival}).  Answered or not: an
     * obligation's answer is what its replay planted at the consumer, and a
     * witness rests only on a value a run compatible with its path
     * delivered (hdfs-17967-pathC rb1: a flip answered the DataNode's key
     * id with 119532 while the moved serial had its producer deliver
     * 119533, and the answer, pinned as a literal, let the solver move the
     * serial past it).  Attested deliveries none of which lowers: what was
     * delivered is unknown and nothing pins it, FREE, named.  No attested
     * delivery (or no producer named) -- the producer ran concretely, or
     * instrumented only in runs that never paired it with this consumer
     * (PV6-18413: taken as a family, no session could send it) -- HELD at
     * the value its row states it received ({@code holds} receives the
     * conjunct, stated under the caller's selector), named "producer
     * unstated" ({@link SmtLowering#unbound}), or settled by rule ({@link
     * #refusedByRule}); a value the lowering places nowhere pins nothing,
     * FREE, named.  Never free by default, never a silent pin, and never a
     * refused conjunction (hdfs-11741 PS1-PS3: the SASL sender's arms were
     * refused for the expiry dates its closure read from a refresh whose
     * NameNode handler no session instrumented, and the key id they would
     * have bound was left HELD).  Inside an arm's body its row names that
     * arm ({@link SmtLowering#arm}).
     *
     * <p>TODO: the family sets aside more than this selection does -- the
     * anchor's work past the path ({@code ComposedFamilies#leftPath}), an
     * arm naming a root its session minted no row for ({@code Arms#arm}),
     * and a message no one run sends at every leaf (its eligibility
     * intersection) -- so an arrival only those leave without a sender is
     * still refused, not settled here.</p>
     */
    private void arrival(String session, AttachRow attach,
                         List<String> holds, List<AttachRow> bound) {
        if (attach.interaction() == null) {
            // No known source, so no family: named, and held below.
            composedFamilies.unpaired(session, attach);
        }
        List<ExportRow> attested = new ArrayList<ExportRow>();
        if (attach.producer() != null) {
            for (ExportRow export : arms.attestedDeliveries(
                    attach.interaction(), session)) {
                // A session a GROW re-run replaces sends no family.
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
        // The one GROW could plan, where the attach names one
        // (Composition#openChain), under the body's spelling of the symbol.
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
        // No producer the corpus attests delivered it.
        String received = JsonFields.firstNonBlank(attach.answeredValue(),
                attach.arrival());
        Refused refused = refusedByRule(attach);
        Delivery delivery = refused == null ? null : delivery(attach);
        if (delivery != null && !delivery.constant) {
            // Its producer's own export carries an expression: bound by it.
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
            // A constant export: the version's constant, or the tick bound.
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

    /**
     * Why no delivery of {@code producer} is attested at an arrival's slot,
     * in words: it ran instrumented in runs none of which paired it with
     * this consumer, or in none.
     */
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

    /**
     * Why no run attests a delivery of a store content leaf at its port --
     * the leaf is here because no attested delivery binds it -- or null
     * where the leaf names no producer: a role, which no weave captures; a
     * daemon tick past the recording's last ({@code
     * Corpus#tickPastRecording}: only a replay slower than the recording ran
     * it); or none ran it instrumented and paired it with this consumer
     * ({@link #unattestedWhy}) where it wrote this port (which tick
     * of a periodic writer writes a document's key is timing: solr-18413
     * SG3C, the Overseer state update that wrote the routing rule's expireAt
     * ran instrumented 21 times, never writing it).  Its own run's export at
     * the port settles the leaf (lead's rule (a), B-a, 2026-10-12): an
     * expression binds it ({@link SmtLowering.Unbound#EXPORTED}, without
     * the producer's path condition -- an over-approximation CONFIRM
     * filters); a constant expression holds it at its version's value, a
     * constant ({@link SmtLowering.Unbound#CONSTANT}) or past the tick bound
     * that bound by name ({@link SmtLowering.Unbound#BOUNDED}); no export
     * that lowers leaves it HELD, an open link, as a leaf with no producer.
     */
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

    /** A store content leaf's producer no session attests at its port
     *  ({@link #refusedByRule}). */
    private static final class Refused {
        final String producer;
        final String rule;
        /** The rule and why, in words. */
        final String why;
        /** TICK_BOUND: the recording's last tick, the bound; else -1. */
        final int bound;

        Refused(String producer, String rule, String why, int bound) {
            this.producer = producer;
            this.rule = rule;
            this.why = rule + ": " + why;
            this.bound = bound;
        }
    }

    /** What a refused producer's own run exported at a leaf's port
     *  ({@link #delivery}). */
    private static final class Delivery {
        /** The leaf stated as one of the exports, with what their lowering
         *  requires of them. */
        final String binding;
        /** Whether every export is a constant expression. */
        final boolean constant;

        Delivery(String binding, boolean constant) {
            this.binding = binding;
            this.constant = constant;
        }
    }

    /**
     * What the leaf's producer exported at its port in the leaf's own run --
     * the delivery the read received ({@link Arms#armsAt}'s selection) --
     * or null where no such export lowers.  Several are its alternatives,
     * each with its lowering's requirements; a constant expression is one
     * that names no symbol.
     */
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
                // Not this alternative; the others may bind (R4).
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

    /**
     * The root a valuation's pin pins (as its symbol is spelled in the pin,
     * {@link Valuation#assertions}), or null where {@code assertion} is no
     * such pin -- a clock's, a pairing's, an own run's hold.
     */
    static String pinnedRoot(String assertion) {
        String opening = "(assert (! (= ";
        if (assertion == null || !assertion.startsWith(opening)
                || !assertion.contains(":named " + VALUATION_PIN)) {
            return null;
        }
        int end = assertion.indexOf(' ', opening.length());
        return end < 0 ? null : assertion.substring(opening.length(), end);
    }

    /** What every valuation's pin is named after ({@link #pinnedRoot}). */
    static final String VALUATION_PIN = "valuation__";

    /** The sort a root's symbol has: a MARKER is a flag, any other a number. */
    static Sort sortOf(RootMintRow row) {
        return row.kind() == RootKind.MARKER ? Sort.BOOL : Sort.INT;
    }

    /**
     * Whether an ATTESTED arm delivers this arrival; if so, declares the
     * symbol at the arm's sort. States NOTHING about the value: the
     * family ({@link ComposedFamilies#closeFamilies}) binds it, and pinning
     * the recorded delivery here too made paths self-contradictory.
     *
     * <p>Declared HERE, during the path's lowering, or leaves naming it in
     * phi or a join are cut as free.  Attested is the delivery's own
     * property ({@link Arms#attestedDeliveries}): a run whose own pairing
     * named this consumer ran the producer instrumented, its export lowered
     * in that session's scope; never ask the consumer's session.</p>
     */
    private boolean attestedArrival(AttachRow attach,
                                    List<ExportRow> attested) {
        // The symbol is the sort its own read parsed; an arm that sent the
        // leaf at another scalar sort binds it through its rendering
        // (SmtLowering#leafEquals), any other is no delivery of it, named,
        // and another may bind: never a refused conjunction (#arrival).
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
            // A read no type states (VALUE) takes the value's sort.
            lowering.declareStated(attach.symbol(), parsed == Sort.VALUE
                    ? delivered.sort : parsed);
            return true;
        }
        return false;
    }

    /**
     * What an attach row states it received, as a term, or null.  An
     * answered value as the wave spells it, a String the solver's literal
     * ({@code runtime.ModelValues#coerce} decodes it so); else the arrival,
     * a String its text whatever it begins with (the mint states the value
     * itself, {@code HandoffMint#publishAttachRow}, {@code
     * StoreContent#attach}: String.valueOf) -- read as a literal, every
     * String arrival held nowhere and went FREE (solr-18413 Z2R: a
     * state.json leaf "active"), and one that begins with a quote was
     * another value.  An empty arrival says nothing.  Any other as the row
     * spells it ({@link SmtLowering#statedValue}).
     */
    private Term arrived(AttachRow attach) {
        String answered = attach.answeredValue() == null ? ""
                : attach.answeredValue().trim();
        if (!answered.isEmpty()) {
            return lowering.statedValue(answered, attach.javaType());
        }
        String arrival = attach.arrival() == null ? "" : attach.arrival();
        if (JavaSmtSorts.sortOfJava(attach.javaType()) == Sort.STRING
                && !arrival.isEmpty()) {
            return Term.nonNullString(VmExpressionIr.quote(arrival), "true");
        }
        return lowering.statedValue(arrival, attach.javaType());
    }

    /**
     * A REFUSAL IS ITS FRAME'S ({@link SmtLowering.RefusalFrame}): an
     * occurrence whose run refused an arrival computed on it as a constant,
     * so a path
     * or an arm whose closure reaches it rests on that arrival's producer,
     * by THE ONE RULE ({@link SmtLowering#unbound}): where the producer the
     * refused attach's handle names rests on what can move, every write of
     * the frame a read joins is FREE over it ({@link SmtLowering#bind}),
     * and the frame is named FREE with those roots; where no row states the
     * producer, or it rests on nothing that moves, its constants hold,
     * named HELD.  Never a refusal.
     */
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

    /**
     * One thing a composed path rests on concretely or leaves unbound, on
     * the path it was composed for ({@code pathId}): a value COMPOSE could
     * not bind ({@link SmtLowering#unbound}: FREE over what its stated
     * producer rests on, which moves, or HELD at its recorded value where no
     * row states its producer -- a read of a version no write states, an
     * arrival no producer attests, a frame), the guard a path left the way
     * at (WAY), a decision stated as a proposition (DECISION).  Information
     * beside the verdict (result.json {@code concrete[]}), never a gap.
     */
    public static final class Concrete {
        public final String kind;
        public final String subject;
        public final String value;
        /** Why, in words. */
        public final String reason;
        public final List<String> movesWith;
        /** The path it was composed on ({@link #on}). */
        public final String pathId;
        /** The arm whose body it is in, null for the path's own ({@link
         *  SmtLowering.Unbound#arm}): a path's row states no arm. */
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

        /** The same row, on this path. */
        Concrete on(String path) {
            return new Concrete(kind, subject, value, reason, movesWith,
                    path, arm);
        }

        /** The same row, in this arm's body. */
        Concrete in(String selector) {
            return new Concrete(kind, subject, value, reason, movesWith,
                    pathId, selector);
        }
    }

    /**
     * The decision prefix of every reached occurrence but the anchor's,
     * by the same rule as the anchor's pi; undeclared names are refused.
     */
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

    /**
     * The locations a family may re-pair that keep the run's own pairing,
     * named: only where a read the family MOVES ({@code moved},
     * {@link #repairing}) would leave something unnamed.  A reader of this
     * path mutated a container through one (R3-REFCONT C-4): a reached
     * occurrence's container version whose mutation names, as its owner, a
     * moved read; another pairing would mutate an object no row records the
     * mutation of.  Or a store of one holds a container through an object
     * that is not it (a {@code Collections} wrapper, a view): a query
     * through that object names no owner, so it is the run's container's
     * answer whichever object the family delivers.  Or a field or a query
     * is asked through a moved container query read: that read names no
     * object (a query states no answer's identity), so no case per writer
     * is the run's.  A reached writer's own read of the location is no
     * moved read (zk-bugs-election-offer: each create and delete looks up
     * its parent in ZooKeeper's node map, the anchor's getData the offer).
     */
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

    /**
     * The container locations whose moved query reads ({@link #repairing})
     * the anchor or a reached occurrence asks a field or a query through
     * ({@code owner}), up to its cutoff.
     */
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

    /**
     * The location of the read a node's {@code owner} is, when that read is
     * a moved one ({@link #repairing}), else null.
     */
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

    /**
     * Whether a reference store stored a container itself, which a wrapper
     * or a view of one is not: the container its referent names, or,
     * refused, an object this session logs the state of.
     */
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

    /**
     * The variables a family of this path may bind: every attach of the
     * anchor (its MESSAGE family, {@link #handoffReads}), and the reads of
     * the locations a STATE family may re-pair.  Independence seeded with
     * phi and the roots alone left out a condition over them, and the
     * family set them free of it (C1 review M2).
     */
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

    /** The reads a STATE family re-pairs on one path ({@link #repairing}). */
    private static final class Repairing {
        /** The reads, in session order. */
        final List<ReadRow> reads = new ArrayList<ReadRow>();
        /** Each read by {@link SmtLowering#readKey}. */
        final Set<String> keys = new LinkedHashSet<String>();
        /** Location key -> the writer the world planted there
         *  ({@link ComposedFamilies#writer}). */
        final Map<String, String> planted =
                new LinkedHashMap<String, String>();
        /** The locations held to the run's pairing ({@link
         *  #pinnedOwners}). */
        Set<String> pinned = Collections.emptySet();
    }

    /**
     * THE READS A STATE FAMILY RE-PAIRS on one path ({@code
     * SmtLowering.SessionJoin#repaired}), ONE entry point: the anchor's,
     * up to its cutoff and every read phi itself names ({@code phiReads},
     * by read event: a target a helper decision decided stands at that
     * decision, and what the guard read after it -- an open arm's {@code
     * f.count} past its {@code f == null} -- is still phi's, as
     * explore.ClosurePlanner#concrete reads it), and every read the
     * session's world planted a
     * pairing on ({@code Corpus.World#pairings}: reader -> writer, as
     * {@code runtime.Confirmation} names them), with every read its
     * occurrence made of the location -- one choice per occurrence's
     * reads, as the replay held them ({@code ConfirmMain#holding}).  One
     * test admits a block of one occurrence's reads of one location: the
     * location owned by a named object, and one of the reads could have
     * seen a writer occurrence besides the one it did ({@link
     * Corpus#eligibleWrites}, the writers the family's arms are drawn
     * from).  A version no row wrote has no writer of its own, so any
     * eligible writer is another; but a read whose only eligible writer is
     * the one it observed, or none, has no alternative: two reads that saw
     * two ordered writers, or a hot field whose earliest versions the VM's
     * version bound dropped and whose only writer is the reader's own
     * occurrence (hdfs-17960 e1c: a configuration parser's fields in the
     * checkpoint saver), stay the run's.  Then a location a reader of the
     * path mutated a container through, or one holding a wrapper, keeps the
     * run's pairing ({@link #pinnedOwners}), planted or not.  A planted
     * location's recorded arm is the recording's pairing, any arm but the
     * plant ({@code ComposedFamilies#stateFamilies}); a pairing whose writer
     * the session states no write of plants nothing.
     */
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
        // (occurrence, location) -> its reads the family would move
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

    /** One occurrence's reads of one location: what a family moves as one
     *  choice. */
    private static String block(ReadRow read) {
        return read.endpoint().occurrence().id() + "|"
                + SmtLowering.locationKey(read.location());
    }

    private static String key(ReadRow read) {
        return SmtLowering.readKey(SmtLowering.locationKey(read.location()),
                read.seq());
    }

    /** Whether one of a block's reads, of a location a named object owns,
     *  could have seen a writer besides the one it did
     *  ({@link #repairing}). */
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

    /**
     * The decisions strictly before {@code before}, polarity applied by
     * {@link Arms#pathCondition} (the rule {@link Arms#wireArms} uses too),
     * lowered in the open scope; a term naming an undeclared symbol is
     * refused by name.
     */
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

    /**
     * Read := the value the ROW states, bound before any lowering: the PIN
     * half of {@link #stateJoins}, hoisted so every leaf naming the symbol
     * resolves.  Only for reads neither the write log nor a mint covers
     * (a root's version is its mint's, whatever the run read): no row
     * states their producer, so each is HELD at that value and named
     * ({@link SmtLowering#unbound}).  Rows stating no value are left to the
     * join half.  {@code answered} keeps one refusal per row across both
     * halves.
     */
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
            if (pin(session, read, refusals, joins, answered)
                    && joins.containsKey(read.symbol())) {
                lowering.held(SmtLowering.locationKey(read.location()) + "@"
                        + read.observedVersion(), read.concreteValue(),
                        "no write row states the version this read saw");
            }
        }
    }

    /**
     * Read := the value its own row states, via
     * {@link SmtLowering#statedValue}.  Answers whether the row states a
     * value at all; an unplaceable one is refused by name.
     */
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

    /** Whether this session's write log covers the version this read saw. */
    private boolean joinable(String session, ReadRow read) {
        return read.observedVersion() >= 0L
                && corpus.writeOf(session,
                SmtLowering.locationKey(read.location()),
                read.observedVersion()) != null;
    }

    /**
     * Read := THE ONE BINDING RULE ({@link SmtLowering#bind}, the guarded
     * read's too, so the two cannot disagree): JOIN, the expression of the
     * write version it observed, if it lowers with no refusal; else its
     * MINT; else PIN; else REFUSE.  A join that refused gives way to the
     * mint, else to a FREE read where what it rests on can move, else to
     * the pin ({@link SmtLowering#unbound}).  No "latest write", no choice
     * between writers.
     */
    void stateJoins(String session, Set<String> occurrences,
                    Independence relevant, SmtLowering.SessionJoin join,
                    List<GapRow> refusals, List<ReadRow> joined,
                    Map<String, String> joins, Set<String> answered) {
        for (ReadRow read : restsOn.statedRows(session, occurrences)) {
            if (read.symbol() == null || read.symbol().isEmpty()) continue;
            if (!relevant.keeps(read)) continue;
            // Family alternatives are for the reads the stage re-pairs: the
            // anchor's, and those the session's world planted a pairing on.
            String key = SmtLowering.locationKey(read.location());
            boolean atAnchor = anchor.id().equals(
                    read.endpoint().occurrence().id())
                    || join.repaired(key, read.seq());
            long version = read.observedVersion();
            WriteRow write = corpus.writeOf(session, key, version);
            if (joins.containsKey(read.symbol())) {
                // Pinned at step 0 to what its row states: a version no row
                // wrote, its writer outside every region.  At the anchor a
                // STATE family may still offer the concurrent writers beside
                // what it returned; a mint's version is a root's.
                if (atAnchor && write == null && version >= 0L
                        && "".equals(SmtLowering.mintedReadSymbol(join,
                        version))) {
                    joined.add(read);
                }
                continue;
            }
            // A cited ref missing from its own table: BLOCKING.
            if (write != null && corpus.expression(session,
                    write.expressionRef()) == null) {
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.BLOCKING, write.expressionRef(),
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
                    // What the JVM evaluated it under holds where it does.
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
                    // The row's own value (non-joinable rows were asked at
                    // step 0, and one it could not place is refused there).
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
                    // Unbound: what it rests on can move, so no pin holds
                    // it ({@link SmtLowering#bind}).
                    lowering.declareStated(read.symbol(),
                            JavaSmtSorts.sortOfJava(read.javaType()));
                    return true;
                }

                @Override
                public Boolean refused(Term value, String subject,
                                       String detail) {
                    refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                            GapClass.DIAGNOSTIC, key + "@" + version,
                            detail));
                    return false;
                }
            };
            // What binding the read required rides with the join that binds
            // it: stated where the conjunction asks about it (#statedJoins).
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

    /**
     * MINT: the read is the symbol the placeholder of its version stated,
     * keyed by {@code mintVersion} alone (CONTRACT v2.4); a root's version
     * moves with the root.  Answers whether it binds the read.
     */
    private boolean mint(String session, ReadRow read, String minted,
                         List<GapRow> refusals, Map<String, String> joins) {
        // This row states the version; bound at step 0.
        if (minted.equals(read.symbol())) return true;
        Sort sort = lowering.declaredSort(minted);
        // A DECLARED ROOT IS BOUND BY ITS DOMAIN, NOT BY A VALUE.  An
        // ordinary read needs a stated value; a clock mint deliberately
        // states none (pinning it could never show a skew), and
        // {@link #clocks} states its domain.
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
            // So the root's domain lands on the joined symbol.
            lowering.declareStated(minted, sort);
        }
        lowering.declareStated(read.symbol(), sort);
        joins.put(read.symbol(), "(= " + read.symbol() + " " + minted + ")");
        return true;
    }

    /**
     * What this session received at these attaches, one term per symbol, as
     * {@link #arrived} reads a row (a String arrival its text).  Kept beside
     * the path, not in it: an arrival is a consequence of its producer's
     * roots, so pinning it would pin them.
     */
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

    // ------------------------------------------------------------------
    // Roots, clocks and the enumeration.
    // ------------------------------------------------------------------

    /** Every root the corpus minted, with what the case says it may be. */
    private void domains() {
        int ordinal = 0;
        for (Map.Entry<String, List<RootMintRow>> entry
                : corpus.roots().entrySet()) {
            RootMintRow row = seedRow(entry.getValue());
            // A CLOCK's domain is {@link #clocks}'s to state.
            if (row.kind() == RootKind.CLOCK) continue;
            RootDomain domain = domainOf(row);
            roots.put(row.rootId(), domain);
            if (!lowering.declared(row.symbol())) continue;
            // A declared marker is free: nothing to assert.
            if (row.kind() == RootKind.MARKER && row.declared()) continue;
            // A root sessions recorded differently has no corpus-wide
            // window; each path carries its own ({@link #valuationOf}).
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
            // No domain: pin to the recording, unless the symbol is also a
            // read (a region input published twice; the join decides).
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

    /**
     * Whether a mint is a declared region INPUT also published as a root.
     * The read wins (it joins to its writer) and the mint pins nothing.
     */
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

    /**
     * Every declared CLOCK cell the formula names: its domain, its reading
     * on the recording's timeline, and its place in its node's order.
     *
     * <p>A cell is one per (root, occurrence), and its reading is where
     * {@link #placeClocks} put it on the recording's timeline before any
     * path composed.  A cell no session can place refused the paths that
     * name it ({@link #unplacedClocks}); one that still reaches the formula
     * is named and has no domain.  Domain ({@link
     * JavaPrimitiveSmtSemantics#clockDomain}): floor = the reading, ceiling
     * = reading + window, unless {@code root-domains.jsonl} declares bounds
     * (the only way to ask for a backward move).</p>
     *
     * <p>ONE ORDER PER CLOCK OF A NODE: a cell is no earlier than the last
     * cell before it by seq -- the event the recording read it at, the order
     * a replay runs a planted clock on in ({@code runtime.NodeClocks}) --
     * that read the same clock ({@link Clock#same}: one JVM clock at one
     * tick; a node's wall clock and a monotonic one are two, and ordering
     * those against each other made every path false; a cell whose row
     * states no JVM clock is on no order, named).  Where the recording's own
     * readings of the two run the other way (two threads between reading
     * and logging), the order gives way by that much, so the recording
     * always satisfies it.  {@code earlierOf} maps each ordered cell to that
     * cell, which the claim runs its clock on from ({@code
     * ClaimPolicy#runsOn}); {@code cells} are in seq order, the order the
     * claim pins them back in.</p>
     */
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

    /**
     * A clock row's host reading, or null (named) when it states no
     * instant.
     */
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

    /**
     * How far each session's host clock read a clock cell later than the
     * recording read it (session -> cell symbol -> milliseconds or ticks of
     * that clock; {@link SmtLowering#clockBases}): its host reading less the
     * recording's, at the cell itself where the recording read it, else at
     * the nearest cell (by seq) of the same clock of the same node that both
     * read -- the same anchor {@link #placed} puts a cell on the recording's
     * timeline by.  The recording's own and a cell no shared cell anchors
     * have none.
     */
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
            // Its cells the recording read too, each with how far late.
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

    /**
     * Every CLOCK root of the corpus on the recording's timeline, before any
     * path composes ({@link #clockTimeline}): a cell the seed read at the
     * seed's host reading; one it never read (a region woven after it, an
     * occurrence a replay moved -- hdfs-17897 NP3: dn0's addKeys under the
     * command queue's anchor, not the heartbeat's) where {@link #placed} puts
     * it; one no session can place, every symbol of it into {@link
     * #unplacedClocks}, which refuses the paths that name it.  The corpus
     * alone decides it: every seed reading anchors, whatever the formula
     * names.
     */
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

    /**
     * Where a cell the recording never read sits on its timeline: for the
     * first session (of {@code rows}) that also read a cell the recording
     * read on the same clock of the same node, the recording's reading of
     * the nearest such cell (by seq, the earlier on a tie) plus the time
     * that session's host read from it to this cell.  Null when no session
     * read one.
     */
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

    /**
     * The session that recorded the run, or null when that has no answer
     * (the corpus's {@code ""} would silently read as "not the seed").
     */
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

    /**
     * Every claim CONFIRM refuted ({@link Refutations}), excluded -- {@code
     * refuted_claim__k} -- its path, the arms it chose there (by their
     * digest: a selector's path ordinal is this composition's, {@link
     * Refutations#atPath}), its valuation and its clocks' region are,
     * together, no model of this formula, so a claim over it is another
     * model or none.  A clock is the claim's region, not its instant: each
     * cell the claim moved jumped the way it did, by any amount, and every
     * other cell runs on from the cell before it, as the claim's replay ran
     * it ({@link #clockStep}) -- an instant alone excluded one point, and
     * the next model sat a tick beside it.  A model whose path or arm this
     * corpus no longer composes cannot recur and is not stated; a root or
     * cell this query does not name constrains nothing.  Roots are named as
     * the valuations name them ({@link Corpus#anyRoot}).
     */
    private void refutations(List<Disjunct> disjuncts,
                             List<String> clockCells,
                             Map<String, Long> clockReadings,
                             Map<String, String> clockBefore) {
        List<Refutations.Refuted> refuted;
        try {
            refuted = Refutations.read(corpus.iteration());
        } catch (java.io.IOException | RuntimeException unreadable) {
            gap(GapKind.CLAIM_REFUTED, GapClass.BLOCKING, Refutations.FILE,
                    "this iteration's refuted claims could not be read, so a claim over it may be "
                            + "one CONFIRM decided against: " + unreadable);
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
            // A moved clock is named by its cell's symbol, at the model's
            // instant: its skew, and each unmoved cell's that of the cell
            // before it, give every cell's step.
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

    /**
     * One clock cell's step against the cell before it on its node's clock
     * ({@code before}): its skew off its reading less that cell's -- {@code
     * sign} 0 equal (the cell runs on), 1 larger (it jumped later), -1
     * smaller (earlier) -- or the cell against its reading where none is
     * before it.  The one spelling of a clock's step, for a witness's pins
     * ({@code ClaimPolicy#runsOn}) and a refuted claim's region ({@link
     * #refutations}).
     */
    static String clockStep(String cell, Map<String, Long> readings,
                            Map<String, String> before, int sign) {
        return clockStep(cell, readings, before,
                sign == 0 ? "=" : sign > 0 ? ">" : "<", 0L);
    }

    /**
     * The same step under {@code relation} against {@code offset} ticks:
     * the cell's skew off its reading less the cell before it's, or the
     * skew alone where none is before it, {@code relation offset} -- a
     * witness's margin on a jump against the clock it runs on from ({@code
     * ClaimPolicy#withMargin}).  Offset 0 is spelled as {@link #clockStep}
     * always spelled a step.
     */
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

    /** The corpus's domain of one root ({@link Corpus#domainOf}). */
    private RootDomain domainOf(RootMintRow row) {
        return corpus.domainOf(row);
    }

    /**
     * One question per declared root; ordinal 0 is the run as it happened,
     * then single moves -- a marker's flip and an integral's domain-end
     * anchors before its other values ({@link #tier}), each by distance, a
     * configuration's after any other move of that distance
     * ({@link #configurationOnly}) --, then pairs.  A declared MARKER flips;
     * an INTEGRAL without a domain is pinned, not enumerated; CLOCKs are not
     * enumerated.  Every skipped root is named: the claim's polarity gate
     * reads which valuations were asked.
     */
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
                // Unnamed by any path: moving it decides nothing, and the pin
                // would name an undeclared constant (a z3 error).
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

    /**
     * Whether moves move configuration only: every moved key a CONFIG root.
     * The one rule a configuration-only witness ranks by -- after a move of
     * any other category at equal distance (#valuations), after every other
     * witness, clocks and pairings included ({@code ClaimPolicy}) -- and the
     * claim states ({@code configurationOnly}, read by triage and findings).
     */
    static boolean configurationOnly(Collection<String> moved,
                                     java.util.function.Function<String,
                                             RootCategory> categoryOf) {
        if (moved.isEmpty()) return false;
        for (String key : moved) {
            if (categoryOf.apply(key) != RootCategory.CONFIG) return false;
        }
        return true;
    }

    /**
     * 0 when every root a move moves sits where a comparison flips -- a
     * marker's flip, an integral at an end anchor of its domain
     * ({@link #anchors}) --, else 1: those values are asked first.
     */
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

    /**
     * An integral domain's end anchors: each bound and its two inward
     * neighbours.  The domain is the hull of its anchors' c - 1, c, c + 1
     * (causynth.ConfigRoots), so its ends are where its outermost
     * comparisons flip, however far from the recording; an interior anchor
     * is not stated past SEED.
     */
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

    /**
     * How far one move is from the recording: |delta| for numeric domains,
     * 1 per moved root otherwise (e.g. a boolean config).
     */
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

    /** What else one declared root may be, ordered by how far it is. */
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
        // A recording outside the domain moves to its nearest bound first.
        if (centre.compareTo(low) < 0 || centre.compareTo(high) > 0) {
            centre = centre.compareTo(low) < 0 ? low : high;
            values.add(centre.toString());
        }
        // The domain's end anchors first, nearest first: a far threshold
        // (a literal 1000 against a recorded 3) is reached under the cap.
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
        // Then outward from the recording, nearest first, within the domain:
        // a wide domain's minimum is no nearer move than any other.
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

    // ------------------------------------------------------------------
    // Reading a published SMT term.
    // ------------------------------------------------------------------

    /**
     * Whether a published term names something nothing declares; if so the
     * path is refused by the missing names (a free constant would answer a
     * question the execution never asked).
     */
    private boolean unknown(String term, List<GapRow> refusals,
                            String subject) {
        List<String> free = new ArrayList<String>();
        // let-bound names are not free.
        Set<String> bound = SmtNames.letBound(term);
        for (String token : SmtNames.names(term)) {
            if (SmtNames.BUILTIN.contains(token)) continue;
            if (bound.contains(token)) continue;
            if (lowering.defined(token)) continue;
            // A recorded symbol may appear only as text.
            if (lowering.declareStated(token)) continue;
            free.add(token);
        }
        if (free.isEmpty()) return false;
        refusals.add(GapRow.of(COMPOSITION, GapKind.UNSTATED_VALUE,
                GapClass.DIAGNOSTIC, subject,
                "this term names symbols nothing declares: " + free));
        return true;
    }

    /** The bound a path stopped on the way to the throw rests on (its
     *  gap's subject suffix, run_engine.sh campaign_bounds). */
    static final String LOOP_BODY_BOUND = "loop-body-bound";

    /** The bound a store content leaf of a producer past the recording's
     *  last daemon tick rests on (its gap's subject suffix, run_engine.sh
     *  campaign_bounds: daemon_tick_bound). */
    static final String DAEMON_TICK_BOUND = "daemon-tick-bound";

    /** The session-id field of a gap the COMPOSITION raised. */
    static final String COMPOSITION = "composition";

    /** The name prefix of the assertions excluding a model CONFIRM refuted
     *  ({@link #refutations}), which an unsat core names. */
    static final String REFUTED_CLAIM = "refuted_claim__";

    /** Whether a name is an exclusion of a model CONFIRM refuted. */
    static boolean excludesAModel(String name) {
        return name != null && name.startsWith(REFUTED_CLAIM);
    }

    /**
     * THE PATH ENDS AT ITS THROW (design 2026-10-12, solr-18413 SG3G/SG3H):
     * the path's anchor occurrence runs the path's decisions up to its fatal
     * decision -- the target decision it throws at, or the guard it leaves
     * the way at -- and no further.  An arm whose producer is the anchor
     * occurrence is no producer for the path where, in its own session, it
     * was delivered after the anchor's last decision at a site and turn the
     * path also decided ({@code site#ordinal}) when that decision left the
     * path (another arm) or is the path's fatal decision itself; in the
     * path's own session, after its fatal decision.  Only the anchor's own
     * rows are ordered, by program order against its own decisions (one
     * occurrence, one thread of work): a producer of any other occurrence is
     * never excluded by where its rows stand (no recorded-order pruning),
     * and leaves only where every arm of a message it was handed is the
     * anchor's work past the path (the nested rule, UNPRODUCIBLE_ANSWER).
     * Where the arm's session never decided at a site and turn the path
     * decided before the delivery, nothing says it left: it stays.
     *
     * @return why the arm is no producer for the path, or null
     */
    String leftPath(Arms.Arm arm) {
        PathEnd end = pathEnd;
        return end == null ? null : end.left(corpus, anchor, arm);
    }

    /** The path being composed, as {@link #leftPath} reads it. */
    private PathEnd pathEnd;

    /** Where one path's anchor occurrence runs ({@link #leftPath}). */
    static final class PathEnd {
        final String session;
        /** The seq of its fatal decision, Long.MAX_VALUE where it states
         *  none (it stopped on the way). */
        final long cutoff;
        /** site#ordinal -> the arm the path took there, up to its fatal
         *  decision. */
        final Map<String, Boolean> taken = new HashMap<String, Boolean>();
        /** The site#ordinal of its fatal decision. */
        final Set<String> fatal = new LinkedHashSet<String>();

        /** One path of {@code session} with these decisions of its anchor
         *  occurrence, whose fatal decision stands at {@code cutoff}. */
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

        /** {@link Composer#leftPath} for the path whose anchor occurrence
         *  is {@code anchor}. */
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
