package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.contract.ComposedManifest;
import edu.uva.liftlab.graphchecker.contract.OccurrenceId;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.contract.RuntimePlanArtifact;
import edu.uva.liftlab.graphchecker.contract.TargetAnchorEvidence;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.concolic.VmTermLowering.and;
import static edu.uva.liftlab.graphchecker.concolic.VmTermLowering.or;

/**
 * The composition, as the design states it.
 *
 * <p>For the anchored target {@code T},
 * {@code Fatal_T = OR_p (pi_p AND phi_p)} over every replay {@code p} that
 * reached {@code T}, conjoined with the declared domains of the roots,
 * lowered by the shared lowering and handed to z3.  Symbolic propagation
 * inside the JVM has already made each replay's fatal value an expression
 * over those roots; the anchor says which rows are about the same event;
 * this class does the merge and nothing else.</p>
 *
 * <p>There is deliberately no read-from model here: no candidate versions,
 * no writer cases, no INITIAL snapshot arms, no last-writer-wins ordering
 * and no compose-time wire binding.  Each path's expressions are resolved
 * inside their own replay by {@link InSessionReadResolver} before they are
 * lowered, and a read that survives that is the propagation cut -- a gate,
 * not something to reconstruct from the region graph.</p>
 *
 * <p>Four gates decide whether the artifact may be believed, and all four
 * are fail-closed:</p>
 *
 * <ul>
 *   <li>{@code TARGET_NOT_REACHED} -- no replay executed the target site;
 *   <li>{@code PROPAGATION_CUT} -- a literal or placeholder stands where an
 *       expression is owed;
 *   <li>{@code CLOSURE_INCOMPLETE} -- a root-dependent branch was left
 *       unflipped, so the disjunction is not the whole disjunction;
 *   <li>{@code RECORDED_ROOT_VALUE_UNSTATED} -- a root in the formula has
 *       no recorded value, so "the root moved" cannot be checked.
 * </ul>
 */
public final class PathMergeComposer {
    public static final int SCHEMA_VERSION = 2;
    public static final String KIND = "CONCOLIC_COMPOSED_SMT";
    public static final String COMPOSER = "PATH_MERGE_V1";
    public static final String MANIFEST_FIELD = "pathMerge";

    /** No replay executed the anchored site. */
    public static final String TARGET_NOT_REACHED = "TARGET_NOT_REACHED";
    /** A value the propagation owed arrived as a literal or a placeholder. */
    public static final String PROPAGATION_CUT = "PROPAGATION_CUT";
    /** A root-dependent branch was never flipped. */
    public static final String CLOSURE_INCOMPLETE = "CLOSURE_INCOMPLETE";
    /** A root in the formula states no recorded value. */
    public static final String RECORDED_ROOT_VALUE_UNSTATED =
            "RECORDED_ROOT_VALUE_UNSTATED";
    /**
     * A root the recording minted that no admitted path's condition or fatal
     * predicate mentions.
     *
     * <p>The formula is then a statement about the program with the program's
     * own free variable missing from it: whatever the solver answers, it
     * answers about constants, and the claim cannot rest on a root it never
     * constrained.  This is the {@code roots: 0} shape, which used to travel
     * all the way to the {@code FINDING_MECHANISM_UNNAMED} blocker after
     * SOLVE -- a statement about the finding rather than about the
     * composition that could not carry one.</p>
     */
    public static final String ROOT_NOT_ON_ANY_PATH =
            "ROOT_NOT_ON_ANY_PATH";

    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();

    private PathMergeComposer() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        Result result = compose(arguments);
        ArtifactIO.replace(arguments.output, result.smtLib);
        result.manifest.add("composedSmtArtifact", ArtifactIO.artifact(
                arguments.output, result.smtLib.getBytes("UTF-8")));
        if (arguments.runtimePlan != null) {
            result.manifest.add("runtimePlanArtifact",
                    ArtifactIO.artifact(arguments.runtimePlan));
        }
        ArtifactIO.replaceJson(arguments.manifest, result.manifest, GSON);
    }

    /** The composed query and the manifest that states what it is. */
    public static final class Result {
        public final String smtLib;
        public final JsonObject manifest;

        Result(String smtLib, JsonObject manifest) {
            this.smtLib = smtLib;
            this.manifest = manifest;
        }
    }

    // ------------------------------------------------------------------
    // Compose.
    // ------------------------------------------------------------------

    public static Result compose(Arguments arguments) throws IOException {
        SharedExpressionTable.Decoder expressions =
                new SharedExpressionTable.Decoder();
        // An anchor this run published no exact reach query for is an anchor
        // no replay reached with a stated path, which is what
        // TARGET_NOT_REACHED says.  It is a refusal about one occurrence, not
        // a failure of the run: the other anchored occurrences still compose,
        // and a campaign that loses its formula because one anchor had no
        // path states nothing about any of them.
        if (arguments.fatalQueries == null
                || !Files.isRegularFile(arguments.fatalQueries)) {
            return refused(arguments, TARGET_NOT_REACHED,
                    "this run published no exact reach query for the "
                            + "selected occurrence: " + arguments.fatalQueries);
        }
        List<JsonObject> queries = expressions.expandAll(
                ArtifactIO.readJsonl(arguments.fatalQueries,
                        "Malformed target reach query %1$s:%2$d",
                        "Non-object target reach query %1$s:%2$d"));
        JsonObject fatal = electQuery(queries, arguments);
        if (fatal == null) {
            return refused(arguments, TARGET_NOT_REACHED,
                    "no target reach query names the selected occurrence");
        }
        List<JsonObject> summaries = new ArrayList<>();
        for (Path path : arguments.summaries) {
            if (path == null || !Files.isRegularFile(path)) continue;
            summaries.addAll(expressions.expandAll(
                    ArtifactIO.readJsonl(path,
                            "Malformed observed summary %1$s:%2$d",
                            "Non-object observed summary %1$s:%2$d")));
        }
        List<RegionInstancePlan> regionPlans = arguments.runtimePlan == null
                ? Collections.<RegionInstancePlan>emptyList()
                : RuntimePlanArtifact.read(arguments.runtimePlan).regionPlans();
        RootInventory roots = RootInventory.of(summaries);
        Map<String, List<JsonObject>> replays = byReplayGroup(summaries);

        String site = optionalString(fatal, "targetSiteId");
        int occurrence = optionalInteger(fatal, "targetOccurrence", 1);
        boolean required = optionalBool(fatal, "requiredTakenOutcome", false);

        PathMergeLowering lowering = new PathMergeLowering(roots.byRawSymbol);
        JsonArray pathRows = new JsonArray();
        JsonArray gates = new JsonArray();
        List<String> selectors = new ArrayList<>();
        List<String> disjuncts = new ArrayList<>();
        JsonArray reachLedger = new JsonArray();
        int ordinal = 0;
        for (JsonElement element : array(fatal, "paths")) {
            if (!element.isJsonObject()) continue;
            JsonObject path = element.getAsJsonObject();
            TargetAnchorEvidence anchor = TargetAnchorEvidence.of(path);
            JsonObject row = new JsonObject();
            int pathOrdinal = ordinal++;
            row.addProperty("pathOrdinal", pathOrdinal);
            row.addProperty("localCaseId",
                    optionalString(path, LocalCaseIdentity.FIELD));
            row.addProperty("replayGroupId",
                    optionalString(path, "replayGroupId"));
            if (anchor == null) {
                row.addProperty("admitted", false);
                row.addProperty("reason", "NO_ANCHOR_EVIDENCE");
                pathRows.add(row);
                gate(gates, TARGET_NOT_REACHED, "path " + pathOrdinal
                        + " publishes no anchored target evidence");
                continue;
            }
            row.addProperty("anchorKey", anchor.key());
            row.addProperty("observedTakenOutcome",
                    anchor.observedTakenOutcome());
            if (!site.equals(anchor.siteId())
                    || occurrence != anchor.occurrence()) {
                row.addProperty("admitted", false);
                row.addProperty("reason", "DIFFERENT_ANCHOR");
                pathRows.add(row);
                continue;
            }
            List<JsonObject> replayGroup = replayRows(replays, path, fatal);
            InSessionReadResolver resolver = InSessionReadResolver.of(
                    replayGroup);
            List<JsonElement> resolved = new ArrayList<>();
            List<String> unresolvedReasons = new ArrayList<>();
            for (JsonElement constraint : anchor.pathCondition()) {
                resolved.add(resolve(resolver, constraint,
                        unresolvedReasons));
            }
            List<JsonElement> rootDecisions = replayRootDecisions(
                    replayGroup, anchor, resolver,
                    roots.byRawSymbol.keySet(), unresolvedReasons);
            resolved.addAll(rootDecisions);
            JsonElement phi = resolve(resolver, anchor.fatalPredicate(),
                    unresolvedReasons);
            // A concrete fatal predicate is not a cut when the path that
            // reached the site is root-dependent.  HDFS-17960 is exactly
            // that shape: the target branch compares two concrete ints
            // (`i != sm.getNumSnapshots()`), and the root reaches it only by
            // control dependence -- on the ordered arm an early return skips
            // the decrement.  The evidence is then the pair of paths: one
            // whose pi holds the root at its recorded value and whose phi is
            // false, one whose pi flips it and whose phi is true.  Refusing
            // the second because its phi carries no symbol throws away the
            // only witness there is.  The cut is real when nothing on this
            // path depends on a root at all -- then a literal phi over
            // declared carriers means the propagation dropped a value.
            boolean rootDependentPath = !rootDecisions.isEmpty();
            for (JsonElement term : resolved) {
                if (mentionsRoot(term, roots.byRawSymbol.keySet())) {
                    rootDependentPath = true;
                    break;
                }
            }
            if (!rootDependentPath) {
                String literalCut = literalOverCarriers(anchor);
                if (!literalCut.isEmpty()) unresolvedReasons.add(literalCut);
            }
            row.addProperty("pathConditionTerms", resolved.size());
            if (!unresolvedReasons.isEmpty()) {
                row.addProperty("admitted", false);
                row.addProperty("reason", PROPAGATION_CUT);
                JsonArray reasons = new JsonArray();
                for (String reason : unresolvedReasons) reasons.add(reason);
                row.add("propagationCuts", reasons);
                pathRows.add(row);
                for (String reason : unresolvedReasons) {
                    gate(gates, PROPAGATION_CUT, "path " + pathOrdinal
                            + ": " + reason);
                }
                continue;
            }
            // One selector per PATH, not per region-local case.  Two
            // replays can traverse the same local case with different
            // values -- that is the whole point of a flip -- and giving
            // them one selector made the exactly-one partition count the
            // same choice twice, which forces it false and leaves the
            // disjunction resting on whatever is left.
            String selector = LocalCaseIdentity.selector(
                    firstNonBlank(optionalString(path,
                            LocalCaseIdentity.FIELD),
                            "path#" + pathOrdinal)
                            + "\0" + optionalString(path, "replayGroupId"));
            lowering.declare(selector, VmTermLowering.Sort.BOOL);
            lowering.beginPath(optionalString(path, "replayGroupId"));
            List<String> terms = new ArrayList<>();
            for (int index = 0; index < resolved.size(); index++) {
                terms.add(lowering.condition(resolved.get(index),
                        "path" + pathOrdinal + ":pi" + index));
            }
            String fatalTerm = lowering.condition(phi,
                    "path" + pathOrdinal + ":phi");
            terms.add(fatalTerm);
            // The definedness facts this path's own lowering raised belong
            // to this path: globally they would constrain its alternatives.
            terms.addAll(lowering.endPath());
            String conjunction = and(terms);
            lowering.assertNamed("path_fatal__" + pathOrdinal,
                    "(=> " + selector + " " + conjunction + ")");
            selectors.add(selector);
            disjuncts.add(conjunction);
            row.addProperty("admitted", true);
            row.addProperty("selector", selector);
            row.addProperty("fatalPredicateTerm", fatalTerm);
            row.addProperty("pathSetClosed",
                    optionalBool(path, "pathSetClosed", false));
            pathRows.add(row);
            reachLedger.add(reachRow(path, anchor, pathOrdinal, selector));
            if (!optionalBool(path, "pathSetClosed", false)) {
                gate(gates, CLOSURE_INCOMPLETE, "path " + pathOrdinal
                        + " left a root-dependent branch unflipped");
            }
        }

        if (selectors.isEmpty()) {
            gate(gates, TARGET_NOT_REACHED,
                    "no replay published a usable anchored row for " + site
                            + "#" + occurrence);
        } else {
            lowering.assertNamed("target_path_partition",
                    exactlyOne(selectors));
            lowering.assertNamed("fatal_target", or(disjuncts));
        }
        for (String subject : lowering.cuts()) {
            gate(gates, PROPAGATION_CUT, subject);
        }

        JsonArray rootRows = new JsonArray();
        for (Map.Entry<String, String> used
                : lowering.rootTerms().entrySet()) {
            JsonObject declared = roots.byRawSymbol.get(used.getValue());
            JsonObject rootRow = roots.materialization(declared,
                    used.getKey());
            if (optionalString(rootRow,
                    ComposedManifest.RECORDED_SOURCE_VALUE).isEmpty()) {
                // The replay that minted this root states the value it read;
                // a replay that was handed a model assignment for it does
                // not, and a run whose only admitted path is such a replay
                // would have no recorded value at all.  The plan states it
                // too, on the symbolize row that named the access, and that
                // is the same recording speaking -- so it is read before the
                // gate refuses, exactly as the claim policy reads it.
                String planned = plannedRecordedValue(regionPlans, rootRow);
                if (!planned.isEmpty()) {
                    rootRow.addProperty(
                            ComposedManifest.RECORDED_SOURCE_VALUE, planned);
                }
            }
            rootRows.add(rootRow);
            if (optionalString(rootRow,
                    ComposedManifest.RECORDED_SOURCE_VALUE).isEmpty()) {
                gate(gates, RECORDED_ROOT_VALUE_UNSTATED,
                        "root " + roots.name(used.getValue())
                                + " as " + used.getKey()
                                + " states no recorded value: neither the"
                                + " replay that minted it nor the plan's"
                                + " symbolize row says what the program"
                                + " read there");
            }
        }

        // Every root the recording minted, against the roots the merge
        // actually lowered.  A minted root outside every pi_p and phi_p is
        // not a smaller formula, it is a different question.
        Set<String> loweredRoots = new LinkedHashSet<>(
                lowering.rootTerms().values());
        for (Map.Entry<String, JsonObject> declared
                : roots.byRawSymbol.entrySet()) {
            if (loweredRoots.contains(declared.getKey())
                    || !roots.minted(declared.getKey())) {
                continue;
            }
            gate(gates, ROOT_NOT_ON_ANY_PATH, "root "
                    + roots.name(declared.getKey())
                    + " was minted at " + roots.sourceKeyOf(declared.getKey())
                    + " and is in no path condition and no fatal predicate"
                    + " of any path admitted at " + site + "#" + occurrence);
        }

        BoundedLoopComposition loops = boundedLoops(regionPlans, fatal);
        JsonObject manifest = manifest(arguments, fatal, site, occurrence,
                required, pathRows, rootRows, reachLedger, gates,
                selectors, lowering, regionPlans, loops);
        return new Result(lowering.render(), manifest);
    }

    // ------------------------------------------------------------------
    // Inputs.
    // ------------------------------------------------------------------

    /** The query row this composition is for. */
    private static JsonObject electQuery(List<JsonObject> queries,
                                         Arguments arguments) {
        JsonObject single = null;
        for (JsonObject query : queries) {
            if (!"TARGET_REACH_PATH_SET_QUERY".equals(
                    optionalString(query, "kind"))) {
                continue;
            }
            if (!arguments.fatalRegion.isEmpty()
                    && !arguments.fatalRegion.equals(
                    optionalString(query, "regionId"))) {
                continue;
            }
            if (!arguments.occurrenceId.isEmpty()
                    && !arguments.occurrenceId.equals(
                    optionalString(query, "occurrenceId"))) {
                continue;
            }
            if (single != null) return null;
            single = query;
        }
        return single;
    }

    private static Map<String, List<JsonObject>> byReplayGroup(
            List<JsonObject> summaries) {
        Map<String, List<JsonObject>> result = new LinkedHashMap<>();
        for (JsonObject summary : summaries) {
            String group = optionalString(summary, "replayGroupId");
            List<JsonObject> rows = result.get(group);
            if (rows == null) {
                rows = new ArrayList<>();
                result.put(group, rows);
            }
            rows.add(summary);
        }
        return result;
    }

    /**
     * Exactly one replay's rows, plus the query itself.
     *
     * <p>Version ids are session-local, so mixing replays would let one
     * execution answer another's read.  The query row joins them only
     * because it carries the same expression table.</p>
     */
    private static List<JsonObject> replayRows(
            Map<String, List<JsonObject>> replays, JsonObject path,
            JsonObject fatal) {
        List<JsonObject> rows = new ArrayList<>();
        List<JsonObject> group = replays.get(
                optionalString(path, "replayGroupId"));
        if (group != null) {
            rows.addAll(group);
            // An imported summary keeps its versions under the recorded
            // shared state; the resolver reads the runtime spelling, so
            // each row is also offered under that name.
            for (JsonObject summary : group) {
                rows.add(versionRow(summary));
            }
        }
        rows.add(versionRow(path));
        rows.add(fatal);
        return rows;
    }

    /**
     * The rest of this replay's root-dependent decisions.
     *
     * <p>A path condition is the replay's, not a region's.  The anchor's own
     * activation publishes the decisions it took, and the composer used to
     * stop there -- so on HDFS-17960 the one decision the whole claim rests
     * on, {@code isSnapshotDeletionOrdered()} inside {@code deleteSnapshot},
     * never entered any pi_p: it is published by a different activation, in
     * a different region, of the same replay.  The formula then constrained
     * no root, and the run said so only after SOLVE.</p>
     *
     * <p>So every activation of this replay group is read, and every
     * decision whose resolved guard mentions a root the recording minted is
     * conjoined.  Conjunction is order-free, which is why this needs no
     * ordering to be correct about what it includes.  What it cannot do
     * today is exclude a decision taken <em>after</em> the anchor: no
     * published member gives one order over the decisions of two
     * activations.  Including one is the safe direction -- a conjunct can
     * only make a disjunct harder to satisfy, never invent a path -- and the
     * exact cut needs a per-replay monotone event id on each decision.</p>
     *
     * <p>A decision that mentions a root and does not resolve is the cut:
     * the replay took it over a value this session cannot state.</p>
     */
    private static List<JsonElement> replayRootDecisions(
            List<JsonObject> replayGroup, TargetAnchorEvidence anchor,
            InSessionReadResolver resolver, Set<String> rootSymbols,
            List<String> unresolvedReasons) {
        List<JsonElement> decisions = new ArrayList<>();
        if (rootSymbols.isEmpty()) return decisions;
        Set<String> held = new LinkedHashSet<>();
        for (JsonElement element : anchor.pathCondition()) {
            held.add(CanonicalJson.render(element));
        }
        for (JsonObject summary : replayGroup) {
            String occurrence = optionalString(summary, "occurrenceId");
            Map<Integer, Long> clocks = decisionClocks(summary);
            JsonArray conditions = array(summary, "pathCondition");
            for (int index = 0; index < conditions.size(); index++) {
                JsonElement constraint = conditions.get(index);
                if (!held.add(CanonicalJson.render(constraint))) continue;
                List<String> reasons = new ArrayList<>();
                JsonElement decision = resolve(resolver, constraint,
                        clocks.getOrDefault(index, 0L), reasons);
                if (!reasons.isEmpty()) {
                    if (mentionsRoot(constraint, rootSymbols)) {
                        unresolvedReasons.add(occurrence
                                + " took a root-dependent decision over a"
                                + " value this replay did not state: "
                                + reasons.get(0));
                    }
                    continue;
                }
                if (mentionsRoot(decision, rootSymbols)) {
                    decisions.add(decision);
                }
            }
        }
        return decisions;
    }

    /**
     * What the plan says the program read at this root's access.
     *
     * <p>Every {@code symbolize} row of the runtime plan carries the
     * {@code primitiveValue} the access returned.  It is matched on the
     * declared field the root names, or on the port when the root is a
     * wire cut, because those are the two names a symbolize row and a
     * materialization share.  Two rows that disagree state nothing: the
     * recording is then not one answer, and a gate is the honest reading.</p>
     */
    private static String plannedRecordedValue(
            List<RegionInstancePlan> regionPlans, JsonObject rootRow) {
        String field = optionalString(rootRow, "fieldSignature");
        String port = optionalString(rootRow, "portId");
        if (field.isEmpty() && port.isEmpty()) return "";
        String held = "";
        for (RegionInstancePlan plan : regionPlans == null
                ? Collections.<RegionInstancePlan>emptyList() : regionPlans) {
            for (JsonElement goal : array(plan.json(), "closureGoals")) {
                if (!goal.isJsonObject()) continue;
                for (JsonElement element
                        : array(goal.getAsJsonObject(), "symbolize")) {
                    if (!element.isJsonObject()) continue;
                    JsonObject row = element.getAsJsonObject();
                    boolean names = !field.isEmpty()
                            && (field.equals(optionalString(row,
                            "leafFieldSignature"))
                            || field.equals(optionalString(row,
                            "accessFieldSignature")))
                            || !port.isEmpty()
                            && port.equals(optionalString(row, "portId"));
                    String value = optionalString(row, "primitiveValue");
                    if (!names || value.isEmpty()) continue;
                    if (held.isEmpty()) {
                        held = value;
                    } else if (!held.equals(value)) {
                        return "";
                    }
                }
            }
        }
        return held;
    }

    /**
     * Which VM event each of this summary's decisions was recorded at.
     *
     * <p>A decision row names the path-condition entry it decided, and the
     * runtime stamps the row with the session event sequence it was recorded
     * at -- the counter that also numbers field versions.  Reading a
     * condition at its own event is what lets a projection over a field
     * written several times name the write that was live when the decision
     * read it.</p>
     */
    private static Map<Integer, Long> decisionClocks(JsonObject summary) {
        Map<Integer, Long> clocks = new LinkedHashMap<>();
        for (JsonElement element : array(summary, "branchMappings")) {
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            int index = JsonFields.exactInteger(mapping,
                    "summaryPcIndex", -1);
            long clock = JsonFields.optionalLongInteger(mapping,
                    InSessionReadResolver.SESSION_EVENT_ID, 0L);
            if (index >= 0 && clock > 0L) clocks.putIfAbsent(index, clock);
        }
        return clocks;
    }

    /** Whether one expression names a root the recording minted. */
    private static boolean mentionsRoot(JsonElement expression,
                                        Set<String> rootSymbols) {
        if (expression == null || expression.isJsonNull()) return false;
        if (expression.isJsonArray()) {
            for (JsonElement child : expression.getAsJsonArray()) {
                if (mentionsRoot(child, rootSymbols)) return true;
            }
            return false;
        }
        if (!expression.isJsonObject()) return false;
        JsonObject node = expression.getAsJsonObject();
        if (rootSymbols.contains(optionalString(node, "_exp"))) return true;
        for (Map.Entry<String, JsonElement> member : node.entrySet()) {
            if (mentionsRoot(member.getValue(), rootSymbols)) return true;
        }
        return false;
    }

    private static JsonObject versionRow(JsonObject owner) {
        JsonObject row = new JsonObject();
        row.add("sharedFieldVersions",
                array(object(owner, SharedStateEvidence.RECORDED_FIELD),
                        "versions"));
        return row;
    }

    private static JsonElement resolve(InSessionReadResolver resolver,
                                       JsonElement expression,
                                       List<String> reasons) {
        return resolve(resolver, expression, 0L, reasons);
    }

    private static JsonElement resolve(InSessionReadResolver resolver,
                                       JsonElement expression,
                                       long vmEventId,
                                       List<String> reasons) {
        JsonElement resolved = resolver.resolve(expression, vmEventId);
        collectUnresolved(resolved, reasons);
        return resolved;
    }

    /**
     * The other shape of the cut: the value arrived already concrete.
     *
     * <p>If the predicate this replay published names no read, no boundary
     * and no symbol at all, then nothing it compares came through
     * propagation -- while the slice declares carriers this activation
     * tracked.  That is a value owed as an expression and delivered as a
     * literal, which is the cut whether or not the literal is right.</p>
     */
    private static String literalOverCarriers(TargetAnchorEvidence anchor) {
        if (anchor.carriers().isEmpty()) return "";
        return propagated(anchor.fatalPredicate()) ? ""
                : "LiteralFatalPredicateOverCarriers:"
                + anchor.carriers().size() + " declared carriers";
    }

    /** Whether an expression names anything propagation carried. */
    private static boolean propagated(JsonElement expression) {
        if (expression == null || expression.isJsonNull()) return false;
        if (expression.isJsonArray()) {
            for (JsonElement element : expression.getAsJsonArray()) {
                if (propagated(element)) return true;
            }
            return false;
        }
        if (!expression.isJsonObject()) return false;
        JsonObject node = expression.getAsJsonObject();
        String type = optionalString(node, "_type");
        if (SharedStateEvidence.GUARDED_READ_TYPE.equals(type)
                || "SymbolExpression".equals(type)
                || VmExpressionIr.CONSUMER_BOUNDARY_TYPE.equals(type)
                || VmExpressionIr.CONSUMER_BOUNDARY_REFERENCE_TYPE
                .equals(type)) {
            return true;
        }
        for (Map.Entry<String, JsonElement> field : node.entrySet()) {
            if (propagated(field.getValue())) return true;
        }
        return false;
    }

    private static void collectUnresolved(JsonElement resolved,
                                          List<String> reasons) {
        if (resolved == null || resolved.isJsonNull()) return;
        if (resolved.isJsonArray()) {
            for (JsonElement element : resolved.getAsJsonArray()) {
                collectUnresolved(element, reasons);
            }
            return;
        }
        if (!resolved.isJsonObject()) return;
        JsonObject node = resolved.getAsJsonObject();
        if (node.has(InSessionReadResolver.UNRESOLVED_TAG)) {
            String reason = optionalString(node,
                    InSessionReadResolver.UNRESOLVED_REASON);
            if (!reasons.contains(reason)) reasons.add(reason);
            return;
        }
        for (Map.Entry<String, JsonElement> field : node.entrySet()) {
            collectUnresolved(field.getValue(), reasons);
        }
    }

    // ------------------------------------------------------------------
    // Roots.
    // ------------------------------------------------------------------

    /**
     * Every root the replays declared, and what each one recorded.
     *
     * <p>A root's recorded value is stated by the replay that observed it;
     * a replay that wrote a model assignment into the field states none.
     * Two replays that state different values leave it unstated, which is
     * a gate rather than a choice.</p>
     */
    static final class RootInventory {
        final Map<String, JsonObject> byRawSymbol = new LinkedHashMap<>();
        /** Raw symbol -> the node and epoch whose recording minted it. */
        private final Map<String, String> sourceKeys = new LinkedHashMap<>();
        private final Map<String, String> recorded = new LinkedHashMap<>();
        /** Every distinct value some replay read at this root. */
        private final Map<String, Set<String>> readings =
                new LinkedHashMap<>();
        private final Set<String> disagreed = new LinkedHashSet<>();

        static RootInventory of(Collection<JsonObject> summaries) {
            RootInventory inventory = new RootInventory();
            for (JsonObject summary : summaries) {
                for (JsonObject event
                        : SymbolicSourceEvidence.eventsOf(summary)) {
                    String raw = optionalString(event, "rawSymbol");
                    if (raw.isEmpty()) continue;
                    inventory.byRawSymbol.putIfAbsent(raw, event);
                    inventory.sourceKeys.putIfAbsent(raw,
                            optionalString(summary, "sourceKey"));
                    String value = SymbolicSourceEvidence
                            .recordedValueOf(event);
                    if (value.isEmpty()) continue;
                    inventory.readings.computeIfAbsent(raw,
                            ignored -> new LinkedHashSet<>()).add(value);
                    String held = inventory.recorded.get(raw);
                    if (held == null) {
                        inventory.recorded.put(raw, value);
                    } else if (!held.equals(value)) {
                        inventory.disagreed.add(raw);
                    }
                }
            }
            return inventory;
        }

        /** Whether the recording states a value this root was minted at. */
        boolean minted(String rawSymbol) {
            return !firstNonBlank(recorded.get(rawSymbol)).isEmpty()
                    || disagreed.contains(rawSymbol);
        }

        /** The node and epoch whose recording minted this root. */
        String sourceKeyOf(String rawSymbol) {
            return firstNonBlank(sourceKeys.get(rawSymbol));
        }

        /** What a reader calls this root: its port, field, or raw symbol. */
        String name(String rawSymbol) {
            JsonObject declared = byRawSymbol.get(rawSymbol);
            if (declared == null) return rawSymbol;
            return firstNonBlank(optionalString(declared, "portId"),
                    firstNonBlank(optionalString(declared, "fieldSignature"),
                            rawSymbol));
        }

        /** One manifest row for one root, as the claim policy reads it. */
        JsonObject materialization(JsonObject declared, String solverTerm) {
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", ComposedManifest
                    .CONFIGURED_SOURCE_MATERIALIZATION_SCHEMA);
            row.addProperty("kind", ComposedManifest
                    .CONFIGURED_SOURCE_MATERIALIZATION_KIND);
            row.addProperty("authority", ComposedManifest
                    .CONFIGURED_SOURCE_MATERIALIZATION_AUTHORITY);
            String raw = declared == null ? ""
                    : optionalString(declared, "rawSymbol");
            row.addProperty("sourceKey",
                    firstNonBlank(sourceKeys.get(raw)));
            for (String member : new String[]{"sourceId", "sourcePhaseId",
                    "sourceOccurrenceId", "fieldSignature", "portId"}) {
                row.addProperty(member, declared == null ? ""
                        : optionalString(declared, member));
            }
            String javaType = declared == null ? ""
                    : optionalString(declared, "javaType");
            VmTermLowering.Sort sort = JavaSmtSorts.sortOfJava(javaType);
            row.addProperty("rawSymbol", raw);
            row.addProperty("javaType", javaType);
            row.addProperty("javaTypeDescriptor", javaType);
            row.addProperty("sort", sort.name());
            row.addProperty("smtSort", sort.smt);
            row.addProperty("solverTerm", solverTerm);
            row.addProperty(ComposedManifest.RECORDED_SOURCE_VALUE,
                    disagreed.contains(raw) ? ""
                            : firstNonBlank(recorded.get(raw)));
            // The contract here is a LIST, comma separated: the readings two
            // mints of one source disagreed on.  Publishing the boolean flag
            // instead made a run with no conflict at all state the string
            // "false" as a reading, which then disagreed with the value the
            // recording actually held -- a root that agreed with itself was
            // refused for contradicting itself.
            row.addProperty(ComposedManifest.RECORDED_VALUE_CONFLICT,
                    disagreed.contains(raw)
                            ? String.join(",", readings.getOrDefault(raw,
                            Collections.<String>emptySet()))
                            : "");
            return row;
        }
    }

    // ------------------------------------------------------------------
    // Output.
    // ------------------------------------------------------------------

    private static String exactlyOne(List<String> selectors) {
        if (selectors.size() == 1) return selectors.get(0);
        StringBuilder sum = new StringBuilder("(= (+");
        for (String selector : selectors) {
            sum.append(" (ite ").append(selector).append(" 1 0)");
        }
        return sum.append(") 1)").toString();
    }

    private static void gate(JsonArray gates, String kind, String detail) {
        JsonObject row = new JsonObject();
        row.addProperty("kind", kind);
        row.addProperty("detail", detail);
        gates.add(row);
    }

    private static JsonObject reachRow(JsonObject path,
                                       TargetAnchorEvidence anchor,
                                       int ordinal, String selector) {
        JsonObject row = new JsonObject();
        row.addProperty("kind", "TARGET_REACH_EVENT");
        row.addProperty("siteId", anchor.siteId());
        row.addProperty("occurrence", anchor.occurrence());
        row.addProperty("outcome", anchor.observedTakenOutcome());
        row.addProperty("attestationRole", optionalString(path,
                TargetReachPathQueryBuilder.TARGET_ATTESTATION_ROLE));
        row.addProperty("sourceObservedOutcome",
                anchor.observedTakenOutcome());
        row.addProperty("desiredTakenOutcome",
                anchor.requiredTakenOutcome());
        row.addProperty("pathOrdinal", ordinal);
        row.addProperty("caseGuard", selector);
        return row;
    }

    private static JsonObject manifest(Arguments arguments, JsonObject fatal,
                                       String site, int occurrence,
                                       boolean required, JsonArray pathRows,
                                       JsonArray rootRows,
                                       JsonArray reachLedger,
                                       JsonArray gates,
                                       List<String> selectors,
                                       PathMergeLowering lowering,
                                       List<RegionInstancePlan> regionPlans,
                                       BoundedLoopComposition loops)
            throws IOException {
        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", SCHEMA_VERSION);
        manifest.addProperty("kind", KIND);
        manifest.addProperty("composer", COMPOSER);
        manifest.addProperty("fatalSite", site);
        manifest.addProperty("targetOccurrence", occurrence);
        manifest.addProperty("requiredTakenOutcome", required);
        manifest.add("targetReachLedger", reachLedger);
        JsonArray partitions = new JsonArray();
        if (!selectors.isEmpty()) {
            JsonArray partition = new JsonArray();
            for (String selector : selectors) partition.add(selector);
            partitions.add(partition);
        }
        manifest.add("caseSelectorPartitions", partitions);
        manifest.add(ComposedManifest.CONDITIONAL_CASE_PARTITIONS,
                new JsonArray());
        manifest.add(ComposedManifest.CONFIGURED_SOURCE_MATERIALIZATION_FIELD,
                rootRows);
        manifest.add(ComposedManifest.MANUAL_SOURCE_MATERIALIZATION_FIELD,
                new JsonArray());
        manifest.add(ComposedManifest.RECORDED_ROOT_VALUES,
                recordedRootValues(rootRows));
        manifest.add(BoundedLoopComposition.MANIFEST_FIELD,
                loops.manifest());
        manifest.add(ClockRootPhysics.MANIFEST_FIELD,
                ClockRootPhysics.manifest(arguments.clockSkewMillis,
                        new ArrayList<JsonObject>()));
        // Ledgers the read-from reconstruction used to publish.  The merge
        // builds no such model, so each one is empty rather than absent:
        // a reader of this artifact must see "there is none", not "the
        // composer forgot to say".
        JsonArray absentKeys = new JsonArray();
        for (JsonObject row : lowering.absentKeyDefaults()) absentKeys.add(row);
        manifest.add(ComposedManifest.ABSENT_KEY_DEFAULTS, absentKeys);
        manifest.add(ComposedManifest.WIRE_FLOW_BINDINGS,
                new JsonArray());
        manifest.add(ComposedManifest.FAULT_CONTROL_GAPS_FIELD,
                new JsonArray());
        manifest.add(ComposedManifest.TARGET_REACH_OCCURRENCES,
                targetReachOccurrences(regionPlans, fatal));

        JsonObject merge = new JsonObject();
        merge.addProperty("schemaVersion", 1);
        merge.addProperty("kind", "PATH_MERGE_COMPOSITION");
        merge.addProperty("authority", COMPOSER);
        merge.addProperty("anchorSiteId", site);
        merge.addProperty("anchorOccurrence", occurrence);
        merge.add("paths", pathRows);
        merge.add("roots", rootRows);
        merge.add("gates", gates);
        JsonArray identities = new JsonArray();
        for (Map.Entry<String, String> identity
                : lowering.opaqueIdentities().entrySet()) {
            JsonObject row = new JsonObject();
            row.addProperty("solverTerm", identity.getKey());
            row.addProperty("rawSymbol", identity.getValue());
            identities.add(row);
        }
        merge.add("executionLocalIdentities", identities);
        merge.addProperty("namedRows", lowering.namedRows());
        manifest.add(MANIFEST_FIELD, merge);

        JsonArray gaps = new JsonArray();
        for (JsonObject row : loops.compositionGaps()) gaps.add(row);
        for (String subject : lowering.unsupported()) {
            JsonObject gap = new JsonObject();
            gap.addProperty("kind", "COMPOSITION_GAP");
            gap.addProperty("subject", subject);
            gap.addProperty("detail", firstNonBlank(
                    lowering.unsupportedDetail().get(subject)));
            gaps.add(gap);
        }
        manifest.add("gaps", gaps);
        boolean ready = gates.size() == 0 && gaps.size() == 0
                && !selectors.isEmpty();
        manifest.addProperty("state",
                ready ? "CANDIDATE_READY" : "CANDIDATE_WITH_GAPS");
        manifest.addProperty(ComposedManifest.FINAL_STATUS,
                ready ? "FINAL_READY" : "FINAL_REFUSED");
        JsonArray refusals = new JsonArray();
        for (JsonElement row : gates) refusals.add(row.deepCopy());
        manifest.add("finalStatusRefusals", refusals);
        manifest.addProperty("pathSetComplete", pathSetComplete(fatal));
        boolean closed = ready && pathSetComplete(fatal);
        manifest.addProperty(ComposedManifest.UNSAT_CLOSURE_COMPLETE,
                closed);
        JsonObject closure = new JsonObject();
        closure.addProperty("schemaVersion", 1);
        closure.addProperty("kind", "UNSAT_CLOSURE_EVIDENCE");
        closure.addProperty("authority", COMPOSER);
        closure.addProperty("targetPathsClosed", pathSetComplete(fatal));
        closure.addProperty("finalStatusReady", ready);
        manifest.add(ComposedManifest.UNSAT_CLOSURE_EVIDENCE, closure);
        manifest.addProperty("symbolicPropagationComplete",
                noCut(gates));
        manifest.add("symbolicPropagationGaps", cutRows(gates));
        return manifest;
    }

    /**
     * Every planned target occurrence, and which one this formula lowered.
     *
     * <p>An annotated failure site executes as many times as the workload
     * runs it, and everything downstream narrows to one of those
     * occurrences: one reach query is built, and this composition is handed
     * exactly that query.  Left unsaid, the narrowing makes a verdict about
     * one execution of the site read as a verdict about the site.  So the
     * whole set is named -- one row per planned occurrence, with the sites
     * it observed and whether this formula reached it -- and the claim can
     * report per occurrence.</p>
     */
    static JsonArray targetReachOccurrences(
            List<RegionInstancePlan> regionPlans, JsonObject fatal) {
        String composedOccurrence = OccurrenceId.parse(
                optionalString(fatal, "occurrenceId")).planned();
        String composedGoal = optionalString(fatal, "goalId");
        JsonArray result = new JsonArray();
        for (RegionInstancePlan plan : regionPlans) {
            for (RegionInstancePlan.Goal goal : plan.goals()) {
                if (!goal.kind().capturesTargetReach()) continue;
                String occurrence = OccurrenceId.parse(
                        plan.occurrenceId()).planned();
                JsonObject row = new JsonObject();
                row.addProperty("occurrenceId", occurrence);
                row.addProperty("regionId", plan.regionId());
                row.addProperty("goalId", goal.goalId());
                row.add("failureSites", observedFailureSites(goal));
                // The goal is the exact address; the occurrence is the
                // fallback for a query that names no goal of its own.
                row.addProperty("composed", composedGoal.isEmpty()
                        ? occurrence.equals(composedOccurrence)
                        : composedGoal.equals(goal.goalId()));
                result.add(row);
            }
        }
        return result;
    }

    /** The failure guards this goal actually observed taking a decision. */
    private static JsonArray observedFailureSites(
            RegionInstancePlan.Goal goal) {
        Set<String> sites = new LinkedHashSet<>();
        for (JsonElement element : goal.branches()) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            if (!optionalBool(branch, "failureTarget", false)
                    || optionalBool(branch, "loopControlGuard", false)
                    || !optionalBool(branch, "observed", false)
                    || !branch.has("requiredOutcome")
                    || branch.get("requiredOutcome").isJsonNull()) {
                continue;
            }
            String site = optionalString(branch, "siteId");
            if (!site.isEmpty()) sites.add(site);
        }
        JsonArray result = new JsonArray();
        for (String site : sites) result.add(site);
        return result;
    }

    private static JsonArray recordedRootValues(JsonArray rootRows) {
        JsonArray values = new JsonArray();
        for (JsonElement element : rootRows) {
            JsonObject root = element.getAsJsonObject();
            JsonObject row = new JsonObject();
            row.addProperty("portId", optionalString(root, "portId"));
            row.addProperty("siteId",
                    optionalString(root, "fieldSignature"));
            row.addProperty("sourceId", optionalString(root, "sourceId"));
            row.addProperty("sourceOccurrenceId",
                    optionalString(root, "sourceOccurrenceId"));
            row.addProperty("fieldSignature",
                    optionalString(root, "fieldSignature"));
            row.addProperty("javaType", optionalString(root, "javaType"));
            row.addProperty("recordedValue",
                    optionalString(root, "recordedValue"));
            row.addProperty("solverTerm",
                    optionalString(root, "solverTerm"));
            row.addProperty("wallClock", false);
            values.add(row);
        }
        return values;
    }

    /**
     * The loop-bound completeness audit over the target's own paths.
     *
     * <p>A merged path is straight-line work between declared bounds, so
     * whether every retained loop of the anchored occurrence carries a
     * count on every path is the one thing that decides whether the
     * disjunction covers the whole behaviour.  It is a gate, not a term:
     * nothing about the formula changes, only whether it may be believed.
     * </p>
     */
    private static BoundedLoopComposition boundedLoops(
            List<RegionInstancePlan> regionPlans, JsonObject fatal) {
        String composed = OccurrenceId.parse(
                optionalString(fatal, "occurrenceId")).planned();
        List<JsonObject> scoped = new ArrayList<>();
        Set<String> held = new LinkedHashSet<>();
        for (RegionInstancePlan plan : regionPlans) {
            String occurrence = OccurrenceId.parse(
                    plan.occurrenceId()).planned();
            if (!occurrence.equals(composed) || !held.add(occurrence)) {
                continue;
            }
            scoped.add(plan.json());
        }
        BoundedLoopComposition loops = BoundedLoopComposition.ofPlanRows(
                scoped, Collections.singletonList(fatal));
        JsonArray paths = array(fatal, "paths");
        for (int index = 0; index < paths.size(); index++) {
            if (!paths.get(index).isJsonObject()) continue;
            JsonObject path = JsonFields.shallowCopy(
                    paths.get(index).getAsJsonObject());
            if (optionalString(path, "caseId").isEmpty()) {
                path.addProperty("caseId", "TARGET_PATH." + index);
            }
            loops.observeCase(optionalString(fatal, "occurrenceId"), path);
        }
        return loops;
    }

    private static boolean pathSetComplete(JsonObject fatal) {
        boolean any = false;
        for (JsonElement element : array(fatal, "paths")) {
            if (!element.isJsonObject()) continue;
            any = true;
            if (!optionalBool(element.getAsJsonObject(), "pathSetClosed",
                    false)) {
                return false;
            }
        }
        return any;
    }

    private static boolean noCut(JsonArray gates) {
        for (JsonElement element : gates) {
            if (PROPAGATION_CUT.equals(optionalString(
                    element.getAsJsonObject(), "kind"))) {
                return false;
            }
        }
        return true;
    }

    private static JsonArray cutRows(JsonArray gates) {
        JsonArray rows = new JsonArray();
        for (JsonElement element : gates) {
            if (PROPAGATION_CUT.equals(optionalString(
                    element.getAsJsonObject(), "kind"))) {
                rows.add(element.deepCopy());
            }
        }
        return rows;
    }

    /** The artifact a composition with nothing to compose publishes. */
    private static Result refused(Arguments arguments, String gate,
                                  String detail) throws IOException {
        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", SCHEMA_VERSION);
        manifest.addProperty("kind", KIND);
        manifest.addProperty("composer", COMPOSER);
        manifest.addProperty("state", "CANDIDATE_WITH_GAPS");
        manifest.addProperty(ComposedManifest.FINAL_STATUS,
                "FINAL_REFUSED");
        JsonArray gates = new JsonArray();
        gate(gates, gate, detail);
        manifest.add("finalStatusRefusals", gates);
        JsonObject merge = new JsonObject();
        merge.addProperty("schemaVersion", 1);
        merge.addProperty("kind", "PATH_MERGE_COMPOSITION");
        merge.add("paths", new JsonArray());
        merge.add("roots", new JsonArray());
        merge.add("gates", gates);
        manifest.add(MANIFEST_FIELD, merge);
        manifest.add("gaps", new JsonArray());
        manifest.add("caseSelectorPartitions", new JsonArray());
        return new Result("(set-logic ALL)\n(assert false)\n(check-sat)\n",
                manifest);
    }

    // ------------------------------------------------------------------
    // CLI.
    // ------------------------------------------------------------------

    /** The composer's arguments, spelled as the old composer spells them. */
    public static final class Arguments {
        Path fatalQueries;
        final List<Path> summaries = new ArrayList<>();
        Path runtimePlan;
        Path output;
        Path manifest;
        String fatalRegion = "";
        String occurrenceId = "";
        Path z3;
        long clockSkewMillis = ClockRootPhysics.DEFAULT_SKEW_MILLIS;

        public static Arguments parse(String[] argv) {
            Arguments result = new Arguments();
            for (int index = 0; index < argv.length; index += 2) {
                String key = argv[index];
                if (index + 1 >= argv.length) {
                    throw new IllegalArgumentException(
                            "missing value for " + key);
                }
                String value = argv[index + 1];
                if ("--fatal-query".equals(key)) {
                    result.fatalQueries = Paths.get(value);
                } else if ("--summaries".equals(key)) {
                    result.summaries.add(Paths.get(value));
                } else if ("--runtime-plan".equals(key)) {
                    result.runtimePlan = Paths.get(value);
                } else if ("--output".equals(key)) {
                    result.output = Paths.get(value);
                } else if ("--manifest".equals(key)) {
                    result.manifest = Paths.get(value);
                } else if ("--fatal-region".equals(key)) {
                    result.fatalRegion = value;
                } else if ("--occurrence-id".equals(key)) {
                    result.occurrenceId = value;
                } else if ("--z3".equals(key)) {
                    result.z3 = value.trim().isEmpty()
                            ? null : Paths.get(value);
                } else if ("--clock-skew-ms".equals(key)) {
                    result.clockSkewMillis = Long.parseLong(value);
                } else if (!"--dead-case-rlimit".equals(key)) {
                    throw new IllegalArgumentException(
                            "unknown option " + key);
                }
            }
            if (result.fatalQueries == null || result.output == null) {
                throw new IllegalArgumentException(
                        "--fatal-query and --output are required");
            }
            if (result.manifest == null) {
                result.manifest = ArtifactIO.sibling(result.output,
                        "composed_smt_manifest.json");
            }
            return result;
        }
    }
}
