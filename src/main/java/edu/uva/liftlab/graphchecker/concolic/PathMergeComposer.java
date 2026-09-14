package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.contract.ComposedManifest;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.HandoffPhaseContract;
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
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
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

    /**
     * The engine label every handoff variable carries.
     *
     * <p>One variable per handoff occurrence, minted by the runtime the way
     * a configured source mints one per source phase -- {@code SRC.} there,
     * {@code HOFF.} here, so the two are told apart by the label and not by
     * a second table.</p>
     */
    static final String HANDOFF_SYMBOL_MARK =
            HandoffPhaseContract.LABEL_PREFIX;

    /** No replay executed the anchored site. */
    public static final String TARGET_NOT_REACHED = "TARGET_NOT_REACHED";
    /** A value the propagation owed arrived as a literal or a placeholder. */
    public static final String PROPAGATION_CUT = "PROPAGATION_CUT";
    /** A path the composition cannot state as the execution that made it. */
    public static final String PATH_NOT_SELF_CONSISTENT =
            "PATH_NOT_SELF_CONSISTENT";
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

        // A handoff row declares a variable of this formula exactly as a
        // symbolization event declares a root: the runtime minted it, named
        // it, and stated its Java type and the value it received.  Without
        // the declaration the lowering meets a scalar it cannot explain and
        // cuts it (UndeclaredFreeSymbol), which refused every path on
        // laneVM12 that carried a wire value -- and it is the row's own
        // javaType that says how to lower it, not the shape of the node the
        // symbol turned up in.
        Map<String, JsonObject> declaredVariables =
                new LinkedHashMap<>(roots.byRawSymbol);
        declaredVariables.putAll(handoffDeclarations(summaries));
        declaredVariables.putAll(manualDeclarations(summaries));
        PathMergeLowering lowering =
                new PathMergeLowering(declaredVariables);
        JsonArray pathRows = new JsonArray();
        JsonArray gates = new JsonArray();
        List<String> selectors = new ArrayList<>();
        JsonArray reachLedger = new JsonArray();
        Set<String> usedHandoffSymbols = new LinkedHashSet<>();
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
            // The valuation this replay ran under is part of pi_p.
            //
            // A replay's assignments are not all visible as decisions: a
            // root can be written and never branched on, and a decision
            // over it can live in a region the anchor's own path condition
            // does not reach.  Either way the execution happened under that
            // value, so the path must say so -- otherwise a path recorded
            // by a flip replay survives at the recorded valuation, which is
            // exactly how laneVM14 came back satisfiable with every marker
            // at the value the healthy run read.
            // Only where this replay ran a root at a value some other
            // replay did not: that is an assignment its obligation applied,
            // and it is what the path has to carry.  A root every replay
            // read the same way is already pinned by its own domain, and
            // asserting it again on every path would put a minted root that
            // nothing branches on "on a path" and silence
            // ROOT_NOT_ON_ANY_PATH.
            for (JsonObject member : replayGroup) {
                for (String conjunct : deliveringValuation(member,
                        declaredVariables, lowering, roots,
                        arguments.clockSkewMillis)) {
                    if (!terms.contains(conjunct)) terms.add(conjunct);
                }
                // An assignment that answered a handoff mint is this path's
                // control, exactly as a root assignment is: the replay ran
                // with v_H at the value the obligation gave it, and a path
                // that does not say so is a path the composition cannot
                // state.  The row's recordedValue is what arrived and stays
                // evidence only.
                for (String conjunct : answeredHandoffs(member,
                        declaredVariables, lowering)) {
                    if (!terms.contains(conjunct)) terms.add(conjunct);
                }
            }
            for (int index = 0; index < resolved.size(); index++) {
                terms.add(lowering.condition(resolved.get(index),
                        "path" + pathOrdinal + ":pi" + index));
            }
            // phi_p is the FATAL arm, not this path's own observation.
            //
            // The anchor states its target decision as the constraint the
            // replay observed -- predicate == observedTakenOutcome -- which
            // is that path's consistency with itself and is true on every
            // path by construction.  Asserting it made a path that decided
            // the target the healthy way satisfiable whenever its own pi
            // was, so the recorded root polarity came back sat and the
            // marker read as not determining.  Fatal_T asks whether the
            // target takes the arm the failure needs: predicate ==
            // requiredTakenOutcome.  Where the path observed that arm the
            // two agree; where it observed the other one the fatal arm is
            // the negation of what it observed, and the path contributes
            // false -- which is exactly what a healthy execution should
            // contribute to "can this fail".
            String observedTerm = lowering.condition(phi,
                    "path" + pathOrdinal + ":phi");
            String fatalTerm = required == anchor.observedTakenOutcome()
                    ? observedTerm : "(not " + observedTerm + ")";
            // INVARIANT: a path must be satisfiable as the execution that
            // made it -- its replay's roots as that replay read them, its
            // clock cells inside its own window, the deliveries it actually
            // received.  A path that is not says the composition has
            // mis-stated that execution, and every answer it then
            // contributes to the disjunction is about the mis-statement.
            // The fatal arm is deliberately NOT part of the question: a
            // healthy path did not take it, and that is not an
            // inconsistency.
            String failing = selfInconsistentConjunct(arguments.z3, lowering,
                    terms, replayDeliveries(replayGroup, declaredVariables,
                            usedHandoffSymbols));
            if (!failing.isEmpty()) {
                row.addProperty("admitted", false);
                row.addProperty("reason", PATH_NOT_SELF_CONSISTENT);
                row.addProperty("failingConjunct", failing);
                pathRows.add(row);
                lowering.endPath();
                gate(gates, PATH_NOT_SELF_CONSISTENT, "path " + pathOrdinal
                        + " (" + optionalString(path, "replayGroupId")
                        + ") is unsatisfiable at its own replay's valuation;"
                        + " the conjunct that closes it is " + failing);
                continue;
            }
            terms.add(fatalTerm);
            // A membership no recording decides is this path's refusal, not
            // a note on the side.  The read still lowers -- to "does this
            // opaque state hold the key", which the solver answers however
            // it likes -- so composing the path anyway would rest the
            // disjunct on a map the recording never showed.
            List<String> refusals = new ArrayList<>();
            for (String subject : lowering.pathRefusals()) {
                if (subject.startsWith(
                        ContainerSmtCodec.CONTAINER_BASE_UNSTATED)) {
                    refusals.add(subject);
                }
            }
            // The definedness facts this path's own lowering raised belong
            // to this path: globally they would constrain its alternatives.
            terms.addAll(lowering.endPath());
            if (!refusals.isEmpty()) {
                row.addProperty("admitted", false);
                row.addProperty("reason", PROPAGATION_CUT);
                JsonArray reasons = new JsonArray();
                for (String subject : refusals) reasons.add(subject);
                row.add("propagationCuts", reasons);
                pathRows.add(row);
                for (String subject : refusals) {
                    gate(gates, PROPAGATION_CUT, "path " + pathOrdinal
                            + ": " + subject);
                }
                continue;
            }
            String conjunction = and(terms);
            lowering.assertNamed("path_fatal__" + pathOrdinal,
                    "(=> " + selector + " " + conjunction + ")");
            selectors.add(selector);
            for (JsonElement term : resolved) {
                collectHandoffSymbols(term, usedHandoffSymbols);
            }
            collectHandoffSymbols(phi, usedHandoffSymbols);
            row.addProperty("admitted", true);
            row.addProperty("selector", selector);
            row.addProperty("fatalPredicateTerm", fatalTerm);
            row.addProperty("pathSetClosed",
                    optionalBool(path, "pathSetClosed", false));
            pathRows.add(row);
            reachLedger.add(reachRow(path, anchor, pathOrdinal, selector));
            if (!optionalBool(path, "pathSetClosed", false)) {
                // With the cause the query states.  A closure that says
                // "not closed" and names nothing is the silence this design
                // forbids: on bug3 the cause was one row away -- the target
                // member's own obligation, solved and then refused because
                // its model assigned handoff variables -- and the gate
                // reported only that something, somewhere, was unflipped.
                gate(gates, CLOSURE_INCOMPLETE, "path " + pathOrdinal
                        + " left a root-dependent branch unflipped: "
                        + closureCause(fatal));
            }
        }

        JsonArray families = handoffFamilies(summaries, replays,
                usedHandoffSymbols, roots, declaredVariables, lowering,
                gates, arguments.clockSkewMillis);
        if (selectors.isEmpty()) {
            gate(gates, TARGET_NOT_REACHED,
                    "no replay published a usable anchored row for " + site
                            + "#" + occurrence);
        } else {
            lowering.assertNamed("target_path_partition",
                    exactlyOne(selectors));
            // The disjunction is over the SELECTORS, not over the path
            // conjunctions again.  Each path already asserts
            // "selector => (pi_p and phi_p)", so asserting that some
            // selector holds says exactly OR_p (pi_p and phi_p) -- while
            // re-inlining the conjunctions here wrote every path's formula
            // into the artifact a second time.  On laneVM14 that one
            // assertion was 45 MB of the file's 91 MB.
            lowering.assertNamed("fatal_target", or(selectors));
        }
        for (String subject : lowering.cuts()) {
            gate(gates, PROPAGATION_CUT, subject);
        }

        // Fatal_T is conjoined with the roots' own domains, and a root's
        // freedom is exactly what the case declares.  Without them the
        // solver reaches the failure by moving whatever is free: on
        // laneVM14's healthy-polarity model the clock cells took
        // -9223372036854775808 and the serial number a value the recording
        // never read, so the polarity with no fault came back satisfiable
        // and the marker read as not determining.  A declared Boolean
        // marker is free in {recorded, flipped} -- both values of a Bool,
        // so nothing to assert.  A clock read is free within the case's
        // declared skew of what it recorded.  Every other root with a
        // recorded value is pinned to it: a value the recording states and
        // the case does not declare varyable is not something the campaign
        // may vary.  A handoff variable is not a root and is constrained by
        // its family alone.
        JsonArray rootRows = new JsonArray();
        int rootDomains = 0;
        for (Map.Entry<String, String> used
                : lowering.rootTerms().entrySet()) {
            // The same map the lowering declared from: a handoff variable
            // is declared by its own row, and reading only the configured
            // roots here left it with no rawSymbol, no javaType and no
            // recorded value -- which is both the malformed materialization
            // row and the unstated recorded value laneVM12 reported.
            JsonObject declared = declaredVariables.get(used.getValue());
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
            String domainTerm = rootDomain(rootRow, declared);
            if (!domainTerm.isEmpty()) {
                lowering.assertNamed("root_domain__" + rootDomains++,
                        domainTerm);
            }
            // A handoff variable is not a root whose movement is a
            // mechanism: it is the value that arrived over a wire, free in
            // this replay's formula and tied back by its family.  Each
            // replay received its own value there, so "the recorded value"
            // is not one thing and nothing reads it as one -- the gate that
            // asks whether a root moved off what the recording read does not
            // apply to it.
            if (!optionalString(declared,
                    InSessionReadResolver.HANDOFF_PHASE_ID).isEmpty()) {
                continue;
            }
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

        // A clock root no admitted path values is otherwise free: the path
        // window is the only one asserted, so the solver parks it at the
        // 64-bit floor and the witness reads back a clock no run returns.
        // The readings the recording states bound it wherever it appears.
        int clockDomains = 0;
        for (String domain : lowering.clockDomains(
                arguments.clockSkewMillis)) {
            lowering.assertNamed("clock_domain__" + clockDomains++, domain);
        }

        BoundedLoopComposition loops = boundedLoops(regionPlans, fatal);
        JsonObject manifest = manifest(arguments, fatal, site, occurrence,
                required, pathRows, rootRows, reachLedger, gates,
                families,
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
    /** Every handoff symbol one resolved expression rests on. */
    private static void collectHandoffSymbols(JsonElement expression,
                                              Set<String> into) {
        if (expression == null || expression.isJsonNull()) return;
        if (expression.isJsonArray()) {
            for (JsonElement element : expression.getAsJsonArray()) {
                collectHandoffSymbols(element, into);
            }
            return;
        }
        if (!expression.isJsonObject()) return;
        JsonObject node = expression.getAsJsonObject();
        if ("SymbolExpression".equals(optionalString(node, "_type"))) {
            String raw = optionalString(node, "_exp");
            if (raw.contains(HANDOFF_SYMBOL_MARK)) into.add(raw);
        }
        for (Map.Entry<String, JsonElement> field : node.entrySet()) {
            collectHandoffSymbols(field.getValue(), into);
        }
    }

    /**
     * The family constraint at each handoff occurrence a path rests on.
     *
     * <p>A value that crossed a wire is a free variable {@code v_H} of the
     * consumer's formula, so a consumer flip is explored without re-running
     * the producer.  What ties it back to the world is this: across every
     * replay of the campaign, the rows published at that same handoff
     * occurrence state the pairs {@code (pi_p, e_p)} -- the producer
     * replay's root-dependent prefix up to the export, and the expression it
     * delivered.  Conjoining {@code OR_p (pi_p^{&lt;H} AND v_H = e_p)} says
     * the received value is one the producer side actually delivers, and
     * under the conditions that made it deliver that one.</p>
     *
     * <p>The join key is the handoff occurrence and nothing else.  A row
     * without {@code handoffPhaseId} or {@code attachEventId} is refused
     * rather than matched on a port, an ordinal or a producer-case search:
     * that was the boundary-family reconstruction this design deleted.</p>
     */
    private static JsonArray handoffFamilies(
            List<JsonObject> summaries,
            Map<String, List<JsonObject>> replays,
            Set<String> usedHandoffSymbols, RootInventory roots,
            Map<String, JsonObject> declaredVariables,
            PathMergeLowering lowering, JsonArray gates,
            long clockSkewMillis) {
        JsonArray published = new JsonArray();
        if (usedHandoffSymbols.isEmpty()) return published;
        Map<String, List<String>> armsBySymbol = new LinkedHashMap<>();
        Map<String, JsonArray> armRowsBySymbol = new LinkedHashMap<>();
        Map<String, String> phaseBySymbol = new LinkedHashMap<>();
        for (JsonObject summary : summaries) {
            for (JsonElement encoded : array(summary, "vmHandoffEvents")) {
                if (!encoded.isJsonObject()) continue;
                JsonObject event = encoded.getAsJsonObject();
                String symbol = optionalString(event,
                        InSessionReadResolver.HANDOFF_SYMBOL);
                if (!usedHandoffSymbols.contains(symbol)) continue;
                String phase = optionalString(event,
                        InSessionReadResolver.HANDOFF_PHASE_ID);
                long export = optionalLongInteger(event,
                        "exportEventId", -1L);
                long attach = optionalLongInteger(event,
                        "attachEventId", -1L);
                // H's identity IS the handoff phase id, by construction:
                // port, consumer address, attach ordinal, element path.  A
                // consumer that minted v_H from a value no producer of this
                // run exported -- a flip replay under one-node linking --
                // states that phase and no VM edge, because there is no edge
                // to state.  It joins its family by the phase like every
                // other row and contributes no arm: it delivered nothing.
                // What it did is on its own path, as the assignment that
                // answered it.  A row that is NOT elementAbsent and still
                // names no attach states no occurrence at all, and stays
                // refused.
                boolean elementAbsent = VmHandoffEvidence.isElementAbsent(
                        event);
                if (phase.isEmpty()
                        || !elementAbsent && (export <= 0L || attach <= 0L)) {
                    gate(gates, PROPAGATION_CUT, "handoff " + symbol
                            + " states no exact occurrence to join on");
                    continue;
                }
                phaseBySymbol.put(symbol, phase);
                if (elementAbsent) continue;
                List<JsonObject> group = replayRows(replays, summary,
                        summary);
                InSessionReadResolver resolver =
                        InSessionReadResolver.of(group);
                List<String> reasons = new ArrayList<>();
                JsonElement delivered = resolve(resolver,
                        event.get(VmHandoffEvidence.EXPRESSION), reasons);
                if (!reasons.isEmpty()) {
                    gate(gates, PROPAGATION_CUT, "handoff " + symbol
                            + " delivered a value this replay did not "
                            + "state: " + reasons.get(0));
                    continue;
                }
                List<String> terms = new ArrayList<>();
                // The valuation this replay ran under.  A delivery is not
                // available under every root valuation: the flip replay that
                // sent one key id ran with the marker at the value its
                // obligation applied, and each replay's own mint rows state
                // what each root produced in it -- the seed's marker row
                // reads false, the flipped replays' read true.  Without this
                // the family was a menu: the recorded polarity could take a
                // delivery only a flipped replay ever made, and reach the
                // failure with no marker moved.
                // Every root this replay ran at a value some other replay
                // did not -- not only the marker.  A root's domain pins it
                // to the value the inventory recorded, which is one
                // replay's; a delivery made by a replay running under a
                // flipped serial number or a moved clock cell was then
                // available at the recorded valuation with nothing
                // contradicting it, because its guard never said which
                // serial number produced it.  Restricting to varied roots
                // is what keeps ROOT_NOT_ON_ANY_PATH honest, exactly as on
                // a path.
                terms.addAll(deliveringValuation(summary, declaredVariables,
                        lowering, roots, clockSkewMillis));
                for (JsonElement decision : producerPrefix(group, resolver,
                        roots.byRawSymbol.keySet(), export)) {
                    terms.add(lowering.condition(decision,
                            "handoff:" + phase + ":pi"));
                }
                // What the CONSUMER read in this replay.  A replay whose
                // obligation answered the mint did not take the producer's
                // expression at all -- the model was written into the leaf
                // at the attach -- so binding the arm to e_p states of that
                // replay something it did not do, and the path that ran it
                // carries v_H = the answer in its own condition.  The two
                // then contradict, which is what refused lane17897g's
                // paths 4 and 9 as not self-consistent.
                String answered = optionalString(event,
                        VmHandoffEvidence.ANSWERED_VALUE);
                JsonElement read = delivered;
                if (!answered.isEmpty()) {
                    read = literalOf(answered, optionalString(
                            declaredVariables.get(symbol), "javaType"));
                    if (read == null) {
                        gate(gates, PROPAGATION_CUT, "handoff " + symbol
                                + " was answered with a value this"
                                + " composition cannot state: " + answered);
                        continue;
                    }
                }
                terms.add(lowering.condition(equals(symbol, read),
                        "handoff:" + phase + ":bind"));
                armsBySymbol.computeIfAbsent(symbol,
                        ignored -> new ArrayList<String>()).add(and(terms));
                // What this arm IS, for a reader of the witness.  A handoff
                // variable is not a root and has no recorded value of its
                // own, so "it moved" is not a thing that can be said about
                // it: the mechanism behind a delivery is the delivering
                // replay's, and the model picks the arm.  The row says
                // which replay, what it delivered, and the valuation it ran
                // under, so the solver reads the mechanism THROUGH the
                // family instead of measuring v_H against one replay's
                // delivery and calling the difference an unexplained move.
                JsonObject arm = new JsonObject();
                arm.addProperty("replayGroupId", optionalString(summary,
                        "replayGroupId"));
                String wire = optionalString(event,
                        ComposedManifest.RECORDED_SOURCE_VALUE);
                arm.addProperty("deliveredValue",
                        answered.isEmpty() ? wire : answered);
                if (!answered.isEmpty()) {
                    // What the wire carried, beside what the consumer read:
                    // the two differ exactly where an obligation answered.
                    arm.addProperty("wireValue", wire);
                }
                arm.add("valuation", armValuation(summary,
                        declaredVariables, roots));
                armRowsBySymbol.computeIfAbsent(symbol,
                        ignored -> new JsonArray()).add(arm);
            }
        }
        for (String symbol : usedHandoffSymbols) {
            List<String> arms = armsBySymbol.get(symbol);
            if (arms == null || arms.isEmpty()) {
                gate(gates, PROPAGATION_CUT, "handoff " + symbol
                        + " is in the formula and no replay published what "
                        + "was delivered at it");
                continue;
            }
            lowering.assertNamed("handoff_family__"
                    + phaseBySymbol.get(symbol).replaceAll(
                            "[^A-Za-z0-9_]", "_"), or(arms));
            JsonObject row = new JsonObject();
            row.addProperty("handoffSymbol", symbol);
            row.addProperty(InSessionReadResolver.HANDOFF_PHASE_ID,
                    phaseBySymbol.get(symbol));
            row.addProperty("pairs", arms.size());
            row.addProperty("handoffSolverTerm", rootTermOf(
                    declaredVariables.get(symbol), symbol));
            JsonArray armRows = armRowsBySymbol.get(symbol);
            row.add("arms", armRows == null ? new JsonArray() : armRows);
            published.add(row);
        }
        return published;
    }

    /**
     * Every manual symbolic input the replays minted, as declarations.
     *
     * <p>A manual input is a root exactly like a configured source, and its
     * identity is what the runtime publishes on the mint row: the manual
     * input id {@code REGION.<r>.in.<uuid>}, the occurrence for a cell that
     * is occurrence-scoped, the Java type and the value it read.  Its
     * {@code symbolicSourceEvidence} row states only the raw symbol and the
     * type, so a materialization built from that alone named no identity at
     * all and the SOLVE stage refused it -- twelve rows on laneVM14, every
     * one a manual input.  The mint row is where the identity is.</p>
     */
    /**
     * The valuation one delivering replay ran under, as rows.
     *
     * <p>The same roots {@link #deliveringValuation} constrains, said as
     * data rather than as SMT: a reader of a witness needs to know which
     * replay's assignment a delivery came with, and what that assignment
     * was, to name the mechanism behind it.</p>
     */
    private static JsonArray armValuation(
            JsonObject summary, Map<String, JsonObject> declaredVariables,
            RootInventory varied) {
        JsonArray rows = new JsonArray();
        Set<String> stated = new LinkedHashSet<>();
        for (String member : new String[]{"symbolicSourceEvidence",
                "manualSymbolicInputObservations"}) {
            for (JsonElement element : array(summary, member)) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject();
                String raw = optionalString(row, "rawSymbol");
                String value = executionReading(row);
                if (raw.isEmpty() || value.isEmpty()
                        || !declaredVariables.containsKey(raw)
                        || !stated.add(raw)) {
                    continue;
                }
                boolean clock = ClockRootPhysics.clockCallee(optionalString(
                        row, SymbolicSourceEvidence.DECLARED_CALLEE));
                if (!clock && varied != null && !varied.varied(raw)) continue;
                JsonObject stated_row = new JsonObject();
                stated_row.addProperty("solverTerm", rootTermOf(
                        declaredVariables.get(raw), raw));
                stated_row.addProperty("value", value);
                stated_row.addProperty("wallClock", clock);
                rows.add(stated_row);
            }
        }
        return rows;
    }

    /**
     * The root valuation one replay ran under, as SMT equalities.
     *
     * <p>Each replay's own mint rows state what every root it minted
     * produced in that execution -- the recorded value for a seed, the
     * applied model value for a replay whose obligation assigned one.  Only
     * roots the formula actually lowered are constrained, and only values
     * that render as a literal.</p>
     */
    static List<String> deliveringValuation(
            JsonObject summary, Map<String, JsonObject> declaredVariables,
            PathMergeLowering lowering, RootInventory varied,
            long clockSkewMillis) {
        List<String> valuation = new ArrayList<>();
        Set<String> stated = new LinkedHashSet<>();
        for (String member : new String[]{"symbolicSourceEvidence",
                "manualSymbolicInputObservations"}) {
            for (JsonElement element : array(summary, member)) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject();
                String raw = optionalString(row, "rawSymbol");
                String value = executionReading(row);
                if (raw.isEmpty() || value.isEmpty()
                        || !declaredVariables.containsKey(raw)
                        || !stated.add(raw)) {
                    continue;
                }
                // A clock is not an assignment a replay ran under: every
                // execution reads it fresh, and two replays of one read read
                // two instants.  So it is never an equality and never
                // filtered by varied() -- it is a window, of the case's
                // declared skew, around what THIS execution read.  One
                // window around one global reading is what left every
                // replay but the one it is centred on unsatisfiable at its
                // own valuation.
                if (ClockRootPhysics.clockCallee(optionalString(row,
                        SymbolicSourceEvidence.DECLARED_CALLEE))) {
                    String term = rootTermOf(
                            declaredVariables.get(raw), raw);
                    String window = clockWindow(term, value,
                            clockSkewMillis);
                    if (!window.isEmpty()) valuation.add(window);
                    // The same reading is this root's own evidence: every
                    // instant any execution read it at bounds it, whether
                    // or not the path this valuation belongs to is
                    // admitted.
                    lowering.observeClockReading(term, value);
                    continue;
                }
                if (varied != null && !varied.varied(raw)) continue;
                String javaType = optionalString(
                        declaredVariables.get(raw), "javaType");
                JsonObject literal = literalOf(value, javaType);
                if (literal == null) continue;
                // Lowered as an expression, not spelled as SMT text: the
                // root may not appear in any path -- a consumer predicate
                // over the arrived value alone does not mention the
                // producer's marker -- and lowering the equality is what
                // declares its term.
                valuation.add(lowering.condition(equals(raw, literal),
                        "handoff:valuation:" + raw));
            }
        }
        return valuation;
    }

    /**
     * What THIS execution read at one mint.
     *
     * <p>{@code recordedValue} on a clock row is the RECORDING's reading --
     * the runtime states it there so a reader has the centre of the case's
     * window.  What this execution read is {@code observedValue} where the
     * runtime states it; a row that states only the one value is read as
     * that execution's own, which is what every non-clock mint row states
     * and what clock rows stated before the recording's reading moved onto
     * them.</p>
     */
    private static String executionReading(JsonObject row) {
        String observed = optionalString(row,
                SymbolicSourceEvidence.OBSERVED_VALUE);
        return observed.isEmpty()
                ? optionalString(row, ComposedManifest.RECORDED_SOURCE_VALUE)
                : observed;
    }

    /** One clock cell's freedom around one reading, or "". */
    private static String clockWindow(String term, String reading,
                                      long skewMillis) {
        if (term.isEmpty() || smtIntegerLiteral(reading).isEmpty()
                || skewMillis <= 0L) {
            return "";
        }
        java.math.BigInteger centre = new java.math.BigInteger(
                reading.trim());
        java.math.BigInteger skew = java.math.BigInteger.valueOf(skewMillis);
        return "(and (>= " + term + " "
                + smtIntegerLiteral(centre.subtract(skew).toString())
                + ") (<= " + term + " "
                + smtIntegerLiteral(centre.add(skew).toString()) + "))";
    }

    /**
     * The one solver name a declared root gets, as the lowering mints it.
     *
     * <p>Spelled here as well because the valuation is built while the
     * paths are lowered, before every root has been met.</p>
     */
    private static String rootTermOf(JsonObject declared, String raw) {
        return JavaSmtSorts.smtName(firstNonBlank(
                optionalString(declared, "symbol"), "sym__" + raw));
    }

    /**
     * What this path's own replay READ at every handoff it used.
     *
     * <p>The family says a delivery is one of the values some replay made
     * there; asking whether THIS path is consistent with itself means
     * asking under the value its own replay read.  Where an obligation
     * answered the mint, that is the answer and not what the wire carried:
     * the model was written into the leaf at the attach, every decision
     * after it was taken on the answer, and asserting the wire's value of
     * that replay contradicts its own decisions -- lane17897g's two paths,
     * closed by {@code (= v_H 119992)} where their replays read 0.</p>
     */
    private static List<String> replayDeliveries(
            List<JsonObject> replayGroup,
            Map<String, JsonObject> declaredVariables,
            Set<String> usedHandoffSymbols) {
        List<String> deliveries = new ArrayList<>();
        Set<String> stated = new LinkedHashSet<>();
        for (JsonObject summary : replayGroup) {
            for (JsonElement element : array(summary, "vmHandoffEvents")) {
                if (!element.isJsonObject()) continue;
                JsonObject event = element.getAsJsonObject();
                String symbol = optionalString(event,
                        InSessionReadResolver.HANDOFF_SYMBOL);
                String value = firstNonBlank(optionalString(event,
                        VmHandoffEvidence.ANSWERED_VALUE),
                        optionalString(event,
                                ComposedManifest.RECORDED_SOURCE_VALUE));
                if (symbol.isEmpty() || value.isEmpty()
                        || !declaredVariables.containsKey(symbol)
                        || smtIntegerLiteral(value).isEmpty()
                        || !stated.add(symbol)) {
                    continue;
                }
                deliveries.add("(= " + rootTermOf(
                        declaredVariables.get(symbol), symbol) + " "
                        + smtIntegerLiteral(value) + ")");
            }
        }
        return deliveries;
    }

    /**
     * The first conjunct that makes this path contradict its own execution,
     * or {@code ""} when it does not.
     *
     * <p>Binary search over the prefix: the shortest prefix that is unsat
     * ends at the conjunct that closed it.</p>
     */
    private static String selfInconsistentConjunct(
            Path z3, PathMergeLowering lowering, List<String> terms,
            List<String> deliveries) {
        if (z3 == null) return "";
        List<String> conjuncts = new ArrayList<>(terms);
        conjuncts.addAll(deliveries);
        if (conjuncts.isEmpty()) return "";
        String preamble = lowering.declarationsOnly();
        if (!"unsat".equals(ask(z3, preamble, conjuncts,
                conjuncts.size()))) {
            return "";
        }
        int low = 1;
        int high = conjuncts.size();
        while (low < high) {
            int middle = (low + high) / 2;
            if ("unsat".equals(ask(z3, preamble, conjuncts, middle))) {
                high = middle;
            } else {
                low = middle + 1;
            }
        }
        String conjunct = conjuncts.get(low - 1);
        return conjunct.length() > 400
                ? conjunct.substring(0, 400) + "..." : conjunct;
    }

    /** One z3 answer over the first {@code count} conjuncts. */
    private static String ask(Path z3, String preamble,
                              List<String> conjuncts, int count) {
        StringBuilder query = new StringBuilder(preamble);
        for (int index = 0; index < count; index++) {
            query.append("(assert ").append(conjuncts.get(index))
                    .append(")\n");
        }
        query.append("(check-sat)\n");
        try {
            Process process = new ProcessBuilder(z3.toString(), "-in",
                    "-smt2").redirectErrorStream(true).start();
            try (java.io.Writer input = new java.io.OutputStreamWriter(
                    process.getOutputStream(),
                    java.nio.charset.StandardCharsets.UTF_8)) {
                input.write(query.toString());
            }
            String last = "";
            try (java.io.BufferedReader output = new java.io.BufferedReader(
                    new java.io.InputStreamReader(process.getInputStream(),
                            java.nio.charset.StandardCharsets.UTF_8))) {
                String line;
                while ((line = output.readLine()) != null) {
                    if (!line.trim().isEmpty()) last = line.trim();
                }
            }
            process.waitFor();
            return last;
        } catch (IOException | InterruptedException unavailable) {
            return "";
        }
    }

    /**
     * The handoff answers this replay ran under, as SMT equalities.
     *
     * <p>A mint an obligation answered returned the model's value, not the
     * one that arrived; the row states both.  The answer is the assignment
     * that made this replay the execution it is, so the path carries it the
     * way it carries a root's value.  A mint nobody answered states no
     * answer and adds nothing.</p>
     */
    private static List<String> answeredHandoffs(
            JsonObject summary, Map<String, JsonObject> declaredVariables,
            PathMergeLowering lowering) {
        List<String> answers = new ArrayList<>();
        Set<String> stated = new LinkedHashSet<>();
        for (JsonElement element : array(summary, "vmHandoffEvents")) {
            if (!element.isJsonObject()) continue;
            JsonObject event = element.getAsJsonObject();
            String symbol = optionalString(event,
                    InSessionReadResolver.HANDOFF_SYMBOL);
            String value = optionalString(event,
                    VmHandoffEvidence.ANSWERED_VALUE);
            if (symbol.isEmpty() || value.isEmpty()
                    || !declaredVariables.containsKey(symbol)
                    || !stated.add(symbol)) {
                continue;
            }
            JsonObject literal = literalOf(value, optionalString(
                    declaredVariables.get(symbol), "javaType"));
            if (literal == null) continue;
            answers.add(lowering.condition(equals(symbol, literal),
                    "handoff:answer:" + symbol));
        }
        return answers;
    }

    /** One recorded value as an expression node, or null. */
    private static JsonObject literalOf(String value, String javaType) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ConstExpr");
        if ("true".equals(value) || "false".equals(value)) {
            node.addProperty("_java_type", "Z");
            node.addProperty("_exp", "true".equals(value) ? "Y_Z_1" : "Y_Z_0");
            return node;
        }
        if (smtIntegerLiteral(value).isEmpty()) return null;
        node.addProperty("_java_type",
                javaType.isEmpty() ? "J" : javaType);
        node.addProperty("_exp", value);
        return node;
    }

    /**
     * What one root may be, as the case declares it, or {@code ""} when the
     * case leaves it free.
     */
    /** Where a case states the lowest value a declared root may take. */
    static final String DECLARED_DOMAIN_MIN = "declaredDomainMin";
    /** Where a case states the highest value a declared root may take. */
    static final String DECLARED_DOMAIN_MAX = "declaredDomainMax";

    static String rootDomain(JsonObject rootRow,
                                     JsonObject declared) {
        String term = optionalString(rootRow, "solverTerm");
        String recorded = optionalString(rootRow,
                ComposedManifest.RECORDED_SOURCE_VALUE);
        if (term.isEmpty() || recorded.isEmpty()) return "";
        // A handoff variable is not a root; its family says what it may be.
        if (declared != null && !optionalString(declared,
                InSessionReadResolver.HANDOFF_PHASE_ID).isEmpty()) {
            return "";
        }
        // A declared marker is free in {recorded, flipped}, which for a
        // Boolean is every value it has.
        if ("BOOL".equals(optionalString(rootRow, "sort"))) return "";
        // A root the case declares a domain for is free inside it: the
        // domain IS what the case says the root may be, so pinning it to
        // the recorded value would answer the case's own question before
        // the solver is asked.  Both bounds or neither -- half a domain
        // states nothing.
        String min = declaredBound(rootRow, declared, DECLARED_DOMAIN_MIN);
        String max = declaredBound(rootRow, declared, DECLARED_DOMAIN_MAX);
        if (!min.isEmpty() && !max.isEmpty()) {
            rootRow.addProperty(DECLARED_DOMAIN_MIN, min);
            rootRow.addProperty(DECLARED_DOMAIN_MAX, max);
            return "(and (>= " + term + " " + smtIntegerLiteral(min)
                    + ") (<= " + term + " " + smtIntegerLiteral(max) + "))";
        }
        String literal = smtIntegerLiteral(recorded);
        if (literal.isEmpty()) return "";
        // A clock read has no global domain: its window is centred on the
        // reading of whichever execution the path is, and one window around
        // one reading contradicts every other replay's decisions over it.
        // The path and the family arm carry it (deliveringValuation).
        if (wallClockRead(rootRow)) return "";
        return "(= " + term + " " + literal + ")";
    }

    /** One bound of a root's declared domain, as an integer, or "". */
    private static String declaredBound(JsonObject rootRow,
                                        JsonObject declared, String member) {
        String stated = optionalString(rootRow, member);
        if (stated.isEmpty() && declared != null) {
            stated = optionalString(declared, member);
        }
        return smtIntegerLiteral(stated).isEmpty() ? "" : stated.trim();
    }

    /**
     * Whether this root is a wall-clock read.
     *
     * <p>By construction, never by site: the mint row states the callee the
     * hook declared, and {@link ClockRootPhysics} names which callees are
     * millisecond clocks.  One predicate answers both the root's domain and
     * the clock ledger, so a root the formula lets move within the window
     * is exactly a root the manifest lists as a clock read.</p>
     */
    private static boolean wallClockRead(JsonObject rootRow) {
        return ClockRootPhysics.clockCallee(optionalString(rootRow,
                SymbolicSourceEvidence.DECLARED_CALLEE));
    }

    /** Every wall-clock root the merge lowered, as ledger rows. */
    private static List<JsonObject> clockReads(JsonArray rootRows,
                                               long clockSkewMillis,
                                               PathMergeLowering lowering) {
        List<JsonObject> reads = new ArrayList<>();
        for (JsonElement element : rootRows) {
            if (!element.isJsonObject()) continue;
            JsonObject read = clockLedgerRow(element.getAsJsonObject(),
                    clockSkewMillis);
            if (read == null) continue;
            // Every instant this root was read at, not only the seed's: a
            // witness is a clock some execution of this case returned, and
            // which execution it is the path says.  A reader that knows
            // only the seed's reading calls a later replay's own instant a
            // move of 320 seconds.
            JsonArray readings = new JsonArray();
            for (String reading : lowering == null
                    ? Collections.<String>emptySet()
                    : lowering.clockReadings(optionalString(read,
                            "solverTerm"))) {
                readings.add(reading);
            }
            if (readings.size() > 0) read.add("readings", readings);
            reads.add(read);
        }
        return reads;
    }

    /** The ledger row for one clock read, or null when it states no value. */
    private static JsonObject clockLedgerRow(JsonObject rootRow,
                                             long clockSkewMillis) {
        if (!wallClockRead(rootRow)) return null;
        String term = optionalString(rootRow, "solverTerm");
        String recorded = optionalString(rootRow,
                ComposedManifest.RECORDED_SOURCE_VALUE);
        if (term.isEmpty() || smtIntegerLiteral(recorded).isEmpty()) {
            return null;
        }
        long value;
        try {
            value = Long.parseLong(recorded.trim());
        } catch (NumberFormatException notIntegral) {
            return null;
        }
        ClockRootPhysics.ClockRead read = new ClockRootPhysics.ClockRead(
                optionalString(rootRow, "sourceKey"),
                optionalString(rootRow, "portId"),
                optionalString(rootRow, "siteId"),
                optionalString(rootRow, "sourceOccurrenceId"),
                optionalLongInteger(rootRow, "eventSeq", -1L), value);
        return ClockRootPhysics.ledgerRow(read, term,
                ClockRootPhysics.window(term, value, clockSkewMillis), "");
    }

    /** An SMT integer literal, negatives in prefix form, or {@code ""}. */
    private static String smtIntegerLiteral(String recorded) {
        try {
            java.math.BigInteger parsed =
                    new java.math.BigInteger(recorded.trim());
            return parsed.signum() < 0
                    ? "(- " + parsed.negate() + ")" : parsed.toString();
        } catch (NumberFormatException notAnInteger) {
            return "";
        }
    }

    /**
     * Every manual symbolic input the replays minted, as declarations.
     *
     * <p>The mint row IS the declaration: it states the identity, the Java
     * type, what the recording read and what this execution read, the port,
     * and the callee the hook declared.  This used to rebuild a declaration
     * from a few of those members, and the rebuilt row -- installed over the
     * evidence row -- lost the port and the callee, so every clock cell in
     * every case came out {@code wallClock false} and no composition ever
     * listed a clock read.  Two spellings of one declaration; the row is the
     * one that exists.</p>
     *
     * <p>A reference is not a root.  Which object this execution ran on is
     * not a value the propagation owes, so it stays the opaque constant the
     * lowering already makes of it; declaring it minted a root term with a
     * Ref sort that the solver's own admission rejects and a recorded value
     * nothing states.</p>
     */
    private static Map<String, JsonObject> manualDeclarations(
            List<JsonObject> summaries) {
        Map<String, JsonObject> declarations = new LinkedHashMap<>();
        for (JsonObject summary : summaries) {
            for (JsonElement encoded
                    : array(summary, "manualSymbolicInputObservations")) {
                if (!encoded.isJsonObject()) continue;
                JsonObject event = encoded.getAsJsonObject();
                String raw = optionalString(event, "rawSymbol");
                if (raw.isEmpty()) continue;
                VmTermLowering.Sort sort = JavaSmtSorts.sortOfJava(
                        optionalString(event, "javaType"));
                if (sort == VmTermLowering.Sort.REF
                        || sort.containerState()) {
                    continue;
                }
                JsonObject declaration =
                        SymbolicSourceEvidence.manualDeclaration(event);
                if (declaration != null) {
                    declarations.putIfAbsent(raw, declaration);
                }
            }
        }
        return declarations;
    }

    /** Every handoff variable the replays minted, as declarations. */
    private static Map<String, JsonObject> handoffDeclarations(
            List<JsonObject> summaries) {
        Map<String, JsonObject> declarations = new LinkedHashMap<>();
        for (JsonObject summary : summaries) {
            for (JsonElement encoded : array(summary, "vmHandoffEvents")) {
                if (!encoded.isJsonObject()) continue;
                JsonObject event = encoded.getAsJsonObject();
                String raw = optionalString(event,
                        InSessionReadResolver.HANDOFF_SYMBOL);
                if (raw.isEmpty()) continue;
                String phase = optionalString(event,
                        InSessionReadResolver.HANDOFF_PHASE_ID);
                // A handoff assignment IS a configured-source assignment
                // whose phase id is the handoff phase id -- one mechanism,
                // by design -- so the declaration states the same members a
                // source materialization does.  Leaving them empty made the
                // SOLVE stage's own admission refuse every one of them
                // (CONFIGURED_SOURCE_MATERIALIZATION_MALFORMED x26 on
                // laneVM14) after COMPOSE had accepted them.
                JsonObject declaration = new JsonObject();
                declaration.addProperty("rawSymbol", raw);
                declaration.addProperty("sourcePhaseId", phase);
                declaration.addProperty("sourceId",
                        optionalString(event, "portId"));
                String consumer = firstNonBlank(optionalString(event,
                        "consumerOccurrenceId"),
                        optionalString(summary, "occurrenceId"));
                // The node and epoch this value arrived on.  A summary that
                // states no sourceKey still names the occurrence, and the
                // occurrence's own prefix is that node -- so the row states
                // its source without a second lookup.
                OccurrenceAddress consumerAddress =
                        OccurrenceAddress.parse(consumer);
                declaration.addProperty("sourceKey",
                        firstNonBlank(optionalString(summary, "sourceKey"),
                                consumerAddress.isNamed()
                                        ? consumerAddress.sourceKey()
                                        : consumer));
                declaration.addProperty("sourceOccurrenceId", consumer);
                declaration.addProperty("fieldSignature",
                        optionalString(event, "portId"));
                declaration.addProperty("javaType",
                        optionalString(event, "javaType"));
                declaration.addProperty(ComposedManifest.RECORDED_SOURCE_VALUE,
                        optionalString(event, "recordedValue"));
                declaration.addProperty(InSessionReadResolver
                        .HANDOFF_PHASE_ID, optionalString(event,
                        InSessionReadResolver.HANDOFF_PHASE_ID));
                declarations.putIfAbsent(raw, declaration);
            }
        }
        return declarations;
    }

    /** {@code v_H = e_p}, as an expression the lowering already knows. */
    private static JsonObject equals(String symbol, JsonElement delivered) {
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_exp", symbol);
        JsonObject node = new JsonObject();
        node.addProperty("_type", "BinaryExpression");
        node.addProperty("_op", "==");
        node.add("_left", left);
        node.add("_right", delivered);
        return node;
    }

    /** One replay's root-dependent decisions taken before the export. */
    private static List<JsonElement> producerPrefix(
            List<JsonObject> group, InSessionReadResolver resolver,
            Set<String> rootSymbols, long exportEventId) {
        List<JsonElement> prefix = new ArrayList<>();
        if (rootSymbols.isEmpty()) return prefix;
        for (JsonObject summary : group) {
            Map<Integer, Long> clocks = decisionClocks(summary);
            JsonArray conditions = array(summary, "pathCondition");
            for (int index = 0; index < conditions.size(); index++) {
                long clock = clocks.getOrDefault(index, 0L);
                if (clock <= 0L || clock >= exportEventId) continue;
                List<String> reasons = new ArrayList<>();
                JsonElement decision = resolve(resolver,
                        conditions.get(index), clock, reasons);
                if (reasons.isEmpty()
                        && mentionsRoot(decision, rootSymbols)) {
                    prefix.add(decision);
                }
            }
        }
        return prefix;
    }

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
        /** (raw symbol, summary) -> the value that execution stated. */
        private final Map<String, String> perSummary = new LinkedHashMap<>();

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
                    // One variable per site, and each replay mints it once
                    // and reads its own value there.  Two replays of a key
                    // rollover read two expiry dates; that is the world
                    // moving, not the recording contradicting itself, and
                    // reading it as a conflict left the root with no
                    // recorded value at all and refused the composition.
                    // A contradiction is one execution stating two values
                    // for one variable, so the disagreement is judged
                    // within a summary and the recorded value is the one
                    // the minting activation stated.
                    String within = raw + "\n"
                            + optionalString(summary, "summaryId");
                    String priorHere = inventory.perSummary.put(within,
                            value);
                    if (priorHere != null && !priorHere.equals(value)) {
                        inventory.disagreed.add(raw);
                    }
                    inventory.recorded.putIfAbsent(raw, value);
                }
                // A manual symbolic input is a root exactly like a
                // configured source, and it is the member every replay
                // publishes its own reading on: the mint evidence carries
                // the seeding activation's reading alone, so judging
                // variation from it said "one value" about a root nine
                // replays read nine ways, and the valuation guard --
                // whose whole filter is varied() -- then constrained
                // neither marker nor any wall-clock cell.  What this
                // member does not do is declare a root: the inventory's
                // materialization and domain still come from the mint.
                for (JsonElement encoded
                        : array(summary, "manualSymbolicInputObservations")) {
                    if (!encoded.isJsonObject()) continue;
                    JsonObject event = encoded.getAsJsonObject();
                    String raw = optionalString(event, "rawSymbol");
                    String value = optionalString(event,
                            ComposedManifest.RECORDED_SOURCE_VALUE);
                    if (raw.isEmpty() || value.isEmpty()) continue;
                    inventory.readings.computeIfAbsent(raw,
                            ignored -> new LinkedHashSet<>()).add(value);
                    String within = raw + "\n"
                            + optionalString(summary, "summaryId");
                    String priorHere = inventory.perSummary.put(within,
                            value);
                    if (priorHere != null && !priorHere.equals(value)) {
                        inventory.disagreed.add(raw);
                    }
                }
            }
            return inventory;
        }

        /** Whether replays of this run read this root differently. */
        boolean varied(String rawSymbol) {
            Set<String> values = readings.get(rawSymbol);
            return values != null && values.size() > 1;
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
            // The inventory knows the node for a root it collected; a
            // declaration that is not one of those -- a handoff variable --
            // states its own.
            row.addProperty("sourceKey",
                    firstNonBlank(sourceKeys.get(raw),
                            declared == null ? ""
                                    : optionalString(declared,
                                    "sourceKey")));
            for (String member : new String[]{"sourceId", "sourcePhaseId",
                    "sourceOccurrenceId", "fieldSignature", "portId",
                    SymbolicSourceEvidence.DECLARED_CALLEE, "siteId",
                    // A handoff variable travels on this row like a root
                    // because the lowering declares it like one -- but it
                    // is not one, and a reader that measures its model
                    // value against "the recorded value" is measuring one
                    // replay's delivery and calling the difference a move.
                    // The phase says which it is.
                    InSessionReadResolver.HANDOFF_PHASE_ID}) {
                row.addProperty(member, declared == null ? ""
                        : optionalString(declared, member));
            }
            row.addProperty("eventSeq", declared == null ? -1L
                    : optionalLongInteger(declared, "eventSeq", -1L));
            String javaType = declared == null ? ""
                    : optionalString(declared, "javaType");
            VmTermLowering.Sort sort = JavaSmtSorts.sortOfJava(javaType);
            row.addProperty("rawSymbol", raw);
            row.addProperty("javaType", javaType);
            row.addProperty("javaTypeDescriptor", javaType);
            row.addProperty("sort", sort.name());
            row.addProperty("smtSort", sort.smt);
            row.addProperty("solverTerm", solverTerm);
            // The inventory states it for a root it collected; a
            // declaration that is not one of those -- a manual input, a
            // handoff variable -- states its own, from the mint row.
            row.addProperty(ComposedManifest.RECORDED_SOURCE_VALUE,
                    disagreed.contains(raw) ? ""
                            : firstNonBlank(recorded.get(raw),
                                    declared == null ? ""
                                            : optionalString(declared,
                                            ComposedManifest
                                                    .RECORDED_SOURCE_VALUE)));
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

    /**
     * Why the path set is not closed, as the query states it.
     *
     * <p>The coverage gaps the closure published travel on the query; each
     * one names the obligation it is about and why that obligation did not
     * close.  A query that states none says so in as many words, which is a
     * reader's cue that the closure withheld a verdict without a reason.</p>
     */
    private static String closureCause(JsonObject fatal) {
        List<String> causes = new ArrayList<>();
        for (JsonElement element : array(fatal, "coverageGaps")) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            String cause = firstNonBlank(optionalString(row, "reason"),
                    optionalString(row, "kind"));
            String subject = optionalString(row, "subject");
            String detail = optionalString(row, "detail");
            causes.add(cause + (subject.isEmpty() ? "" : " on " + subject)
                    + (detail.isEmpty() ? "" : " (" + detail + ")"));
        }
        return causes.isEmpty()
                ? "the path set states no cause for withholding closure"
                : String.join("; ", causes);
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
                                       JsonArray handoffFamilies,
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
        // The ledger lists exactly the roots whose domain the merge widened
        // to a window, because both read the one predicate over the same
        // rows.  Composing it from an empty list left every clock pinned to
        // one replay's reading -- eleven of bug3's twelve paths
        // unsatisfiable at every valuation, and clockDecisions refusing to
        // probe at all with NO_CLOCK_ROOT.
        manifest.add(ClockRootPhysics.MANIFEST_FIELD,
                ClockRootPhysics.manifest(arguments.clockSkewMillis,
                        clockReads(rootRows, arguments.clockSkewMillis,
                                lowering)));
        // Ledgers the read-from reconstruction used to publish.  The merge
        // builds no such model, so each one is empty rather than absent:
        // a reader of this artifact must see "there is none", not "the
        // composer forgot to say".
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
        merge.add("handoffFamilies", handoffFamilies);
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
        // CLOSURE_INCOMPLETE says a root-dependent branch somewhere was
        // left unflipped, which is what withholds a *closed UNSAT*
        // conclusion -- pathSetComplete below carries it to exactly that
        // reading.  A satisfying witness on the paths that were admitted is
        // a finding whatever remains unexplored elsewhere, so it is not a
        // refusal of the composition: treating it as one withheld
        // FINAL_READY from every laneVM12 anchor that had a witness.
        int refusing = 0;
        for (JsonElement row : gates) {
            if (!CLOSURE_INCOMPLETE.equals(optionalString(
                    row.getAsJsonObject(), "kind"))) {
                refusing++;
            }
        }
        boolean ready = refusing == 0 && gaps.size() == 0
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
            row.addProperty("wallClock", wallClockRead(root));
            // Carried so a reader can tell a handoff variable from a root
            // without matching on a symbol's spelling.
            row.addProperty(InSessionReadResolver.HANDOFF_PHASE_ID,
                    optionalString(root,
                            InSessionReadResolver.HANDOFF_PHASE_ID));
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
