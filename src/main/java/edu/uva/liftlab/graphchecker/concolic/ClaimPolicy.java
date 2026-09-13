package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.contract.ComposedManifest;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

import edu.uva.liftlab.graphchecker.contract.GapLedger;

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
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * The one decision that states what a campaign proved.
 *
 * <p>The campaign acceptance gate used to be jq in the EMIT stage of
 * {@code run_engine.sh}: it read the Composer's stage-local
 * {@code finalStatus}, the solver's {@code reachability} and one degeneracy
 * string, and published {@code SAT_CANDIDATE} from them. That accepted a run
 * whose witness the solver could not tie to any symbolic root -- an
 * {@code UNDECIDED_*} degeneracy verdict was not a refusal, a declared
 * cross-node {@code WIRE_FLOW} that reached no consumer boundary family was
 * not visible to it, and a witness identical under every enumerated valuation
 * read exactly like a witness the target constrains.</p>
 *
 * <p>So the claim is decided here, once, from the recorded evidence, and every
 * reason it is not accepted is published as a named blocker rather than folded
 * into one prose sentence. {@code finalStatus: FINAL_READY} keeps its
 * stage-local meaning -- the emitted formula is structurally complete -- and
 * is one input to this gate instead of the gate itself.</p>
 */
public final class ClaimPolicy {
    /** Where the decision is published inside the reach-condition report. */
    public static final String CLAIM = "campaignClaim";
    static final String KIND = "CAMPAIGN_CLAIM";
    /** The {@code kind} the communication mappings declare each flow with. */
    /** The {@code kind} the Composer names a consumer boundary family with. */
    private static final String CONSUMER_BOUNDARY_KIND =
            "CONSUMER_BOUNDARY_CASE_DEPENDENCY";
    /** Every region identity the manifest and the runtime plan share. */
    private static final Pattern REGION_ID =
            Pattern.compile("REGION\\.[0-9a-fA-F-]{36}");

    /** A bounded witness the target predicate ties to a symbolic root. */
    public static final String SAT_CANDIDATE = "SAT_CANDIDATE";
    /** The composed bounded model is closed and unsatisfiable. */
    public static final String UNSAT_CLOSED = "UNSAT_CLOSED";
    /** No accepted claim; every reason is a named blocker. */
    public static final String INCONCLUSIVE_PARTIAL = "INCONCLUSIVE_PARTIAL";

    /** The Composer refused the composition it published. */
    static final String COMPOSER_NOT_FINAL_READY =
            "COMPOSER_NOT_FINAL_READY";
    /** A formula or solver gap is still open on the selected path set. */
    static final String COMPOSITION_GAPS_UNRESOLVED =
            "COMPOSITION_GAPS_UNRESOLVED";
    /** The target predicate is provably free of every symbolic root. */
    static final String DEGENERATE_ROOT_SPACE = "DEGENERATE_ROOT_SPACE";
    /** The degeneracy question was never decided, so it is not answered. */
    static final String UNDECIDED_ROOT_SPACE = "UNDECIDED_ROOT_SPACE";
    /** No root flip changed satisfiability: the witness is not fault-sensitive. */
    static final String TARGET_UNCONSTRAINED_BY_ROOTS =
            "TARGET_UNCONSTRAINED_BY_ROOTS";
    /** The existential witness carries no information about the target. */
    static final String WITNESS_UNINFORMATIVE = "WITNESS_UNINFORMATIVE";
    /**
     * The witness reads the fatal value out of an initial container state the
     * composition reported it could not reconstruct.
     */
    /** The mapping field naming where a flow's value lands on arrival. */
    /** The wire's own boundary family reached a term. */
    static final String PORT_FAMILY = "PORT_FAMILY";
    /** The field the consumer assigned it to is read in the formula. */
    /** The solver returned neither sat nor unsat on an enumerated valuation. */
    static final String SOLVER_UNDECIDED_VALUATIONS =
            "SOLVER_UNDECIDED_VALUATIONS";
    /** An UNSAT result without closed selected-path authority is not closed. */
    static final String UNSAT_CLOSURE_INCOMPLETE = "UNSAT_CLOSURE_INCOMPLETE";
    /**
     * The composed body is unsatisfiable before any polarity is asserted.
     *
     * <p>Every valuation of such a composition answers {@code unsat}, so the
     * solver stage reports {@code UNREACHABLE} and the claim reads as a
     * refutation of the target -- when what was refuted is the model. The
     * composer's own formula probe is the only place that distinction is
     * made ({@link DeadCaseLemmas}, published as
     * {@value DeadCaseLemmas#FORMULA_UNSAT_ROW}), and it is read here so the
     * verdict layer states it rather than inheriting a
     * {@link #UNSAT_CLOSED} from a contradiction. HDFS-17899 bug3 met this
     * under the replay-group identity axiom: all four marker valuations
     * unsat, no composition gap, and the contradiction two commits
     * upstream.</p>
     */
    static final String COMPOSED_BODY_UNSATISFIABLE =
            "COMPOSED_BODY_UNSATISFIABLE";
    /** The solver stage reached no exact reachability decision. */
    static final String NO_EXACT_REACHABILITY = "NO_EXACT_REACHABILITY";
    /**
     * The experiment injects a fault marker and the target is reachable in
     * both of its polarities with nothing else named to explain the other one.
     */
    static final String FAULT_MARKER_NOT_DETERMINING =
            "FAULT_MARKER_NOT_DETERMINING";
    /**
     * A satisfying witness rests on freedom no named mechanism accounts for.
     *
     * <p>This is the blocker the acceptance ruling leaves: a SAT witness is a
     * finding when everything it moved is something the world does -- a marker
     * flip, drift inside the recorded clock window, a rotation race the
     * recorded write order states -- and is withheld only where the witness
     * was free in a way nobody wrote down. The freedoms that already carry a
     * blocker of their own ({@link #UNDECIDED_ROOT_SPACE}) are not named
     * twice; this one covers the freedom that lives in the witness
     * itself.</p>
     */
    static final String WITNESS_FREEDOM_UNEXPLAINED =
            "WITNESS_FREEDOM_UNEXPLAINED";
    /**
     * The experiment plants a fault and the polarity that has it is not a
     * satisfied, explained witness.
     *
     * <p>Accepting a SAT candidate is a statement about the bug the campaign
     * went looking for, so the buggy polarity has to be the one that produced
     * an explained witness. A run whose only witness is in the other polarity
     * is a finding about that polarity and not the claim this campaign made.
     * </p>
     */
    static final String FAULT_POLARITY_NOT_WITNESSED =
            "FAULT_POLARITY_NOT_WITNESSED";
    /**
     * A declared marker every flip of which is unsatisfiable.
     *
     * <p>An experiment may plant more than one marker, and they need not all
     * be the bug. hdfs-17899-bug1 plants two on the Balancer: the constructor's
     * {@code updateBlockKeys} at occurrence #1 and the {@code BlockKeyUpdater}
     * thread's periodic {@code getBlockKeys} at occurrence #5, whose catch at
     * {@code KeyManager.java:168-170} is the path production tolerates. Failing
     * the constructor's call aborts the test outright, so every valuation that
     * flips it is unsatisfiable -- that marker is not the mechanism, which is a
     * fact worth publishing and not a reason to withhold the run.</p>
     */
    static final String NOT_A_MECHANISM = "NOT_A_MECHANISM";
    /**
     * A declared Boolean root nothing observed a recorded value for.
     *
     * <p>Every judgement this policy makes about a root is a comparison with
     * what the recording had: "flipped", "reproduced", "the other polarity",
     * the whole marker evidence block. With no recorded value there is
     * nothing to compare against, and the run has to say so rather than
     * assume one. The assumption this replaces read an unstated root as
     * {@code true}, which turned HDFS-17960's satisfying witness at the
     * recorded {@code false} into a flip and published "a symbolic root
     * flips it" with an empty mechanism list.</p>
     *
     * <p>The value exists: the VM holds the field's concrete content at the
     * mint that symbolizes it, and the plan holds the port's
     * {@code primitiveValue}. A root that reaches here without one is a
     * reporting gap in the recording, and it withholds the claim.</p>
     */
    static final String RECORDED_ROOT_VALUE_UNSTATED =
            "RECORDED_ROOT_VALUE_UNSTATED";
    /**
     * Two sources observed one root and stated different recorded values.
     *
     * <p>A contradiction about the recording, not an absence of one. The
     * blocker names both values and the source that stated each, so a reader
     * can go and find out which mint read what instead of being handed a
     * root the run quietly treats as unknown.</p>
     */
    static final String RECORDED_ROOT_VALUE_DISAGREEMENT =
            "RECORDED_ROOT_VALUE_DISAGREEMENT";
    /**
     * A satisfying witness the run would rest on that names no mechanism.
     *
     * <p>A SAT answer is a statement about the formula. A finding is a
     * statement about the program, and it needs a named way the program
     * could have done it: a marker flipped, a rotation race the recorded
     * order states, a clock moved inside its window and shown to be needed,
     * or the recorded valuation itself reaching the target while every flip
     * of a root is refuted. {@link WitnessLegitimacy#FINDING_KIND} names
     * which; where it names none there is no finding, and the run says so
     * instead of publishing a reachable verdict with an empty mechanism
     * list.</p>
     */
    static final String FINDING_MECHANISM_UNNAMED =
            "FINDING_MECHANISM_UNNAMED";
    /**
     * The accepted witness moved a planted marker off what it recorded.
     *
     * <p>The shape a fault-injection campaign claims: the experiment planted
     * the fault, and the polarity that has it is what reaches the target.</p>
     */
    static final String FLIPPED_PLANTED_MARKER = "FLIPPED_PLANTED_MARKER";
    /**
     * The accepted witness left every declared root at what it recorded.
     *
     * <p>The shape a run with no planted marker claims: nothing was injected,
     * and the witness reproduces the failure the recording already had.
     * HDFS-17960 is one -- its only root is the configured
     * {@code snapshot.deletion.ordered} field, recorded {@code false}, and
     * the satisfying valuation is that same {@code false}.</p>
     */
    static final String RECORDED_ROOT_VALUES_REPRODUCED =
            "RECORDED_ROOT_VALUES_REPRODUCED";
    /**
     * The accepted witness moved a root nobody planted.
     *
     * <p>Neither shape: no fault was injected, and the witness still does not
     * sit at what the roots recorded. Most often that is a root whose
     * recorded value nothing stated, so "moved" is measured against a
     * default -- which is exactly the reading that has to be visible rather
     * than folded into one of the other two names.</p>
     */
    static final String UNPLANTED_ROOT_MOVED = "UNPLANTED_ROOT_MOVED";
    /**
     * An observed occurrence of the annotated target that this composition
     * did not lower.
     *
     * <p>The planner plants a target-reach goal on every execution of the
     * annotated site, and everything after it narrows to one: the workflow
     * elects a single {@code TARGET} member, the campaign builds a reach
     * query for that member alone, and the composition lowers that query.
     * A verdict about one execution then reads as a verdict about the site.
     * hdfs-17897 is the case in point -- the elected occurrence is the
     * DataNode-to-DataNode SASL handshake, while the bug's chain ends at the
     * client's handshake, which is therefore off the slice entirely.</p>
     *
     * <p>Reported rather than blocking: the composed formula is a true
     * statement about the occurrence it lowered.  What it is not is a
     * statement about the others, and this names each one.</p>
     */
    static final String TARGET_OCCURRENCE_NOT_COMPOSED =
            "TARGET_OCCURRENCE_NOT_COMPOSED";

    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();

    private ClaimPolicy() {
    }

    /**
     * Replays the gate on already published artifacts. The recorded
     * composition manifest and reach-condition report are the only evidence,
     * so a final directory from any earlier run can be re-decided without
     * re-running the campaign.
     */
    public static void main(String[] argv) throws Exception {
        Map<String, String> values = new LinkedHashMap<>();
        for (int index = 0; argv != null && index < argv.length; index++) {
            String option = argv[index];
            if (option == null || !option.startsWith("--")
                    || index + 1 >= argv.length) {
                throw new IllegalArgumentException(
                        "Expected --name value, got " + option);
            }
            String key = option.substring(2);
            if (!"manifest".equals(key) && !"reach".equals(key)
                    && !"plan".equals(key)) {
                throw new IllegalArgumentException(
                        "Unknown claim option: --" + key);
            }
            values.put(key, argv[++index]);
        }
        JsonObject manifest = ArtifactIO.readObject(
                required(values, "manifest"));
        JsonObject reach = ArtifactIO.readObject(required(values, "reach"));
        // The plan the composition pinned is the plan that bound its exchange
        // ports, so a replay needs no argument to find it.
        String plan = values.get("plan");
        if (plan == null || plan.trim().isEmpty()) {
            plan = optionalString(object(manifest, "runtimePlanArtifact"),
                    "path");
        }
        JsonObject claim = decide(manifest, reach,
                PlannedSymbolicRoots.read(plan));
        System.out.println(GSON.toJson(claim));
        if (!accepted(optionalString(claim, "claim"))) {
            System.exit(2);
        }
    }

    private static Path required(Map<String, String> values, String key) {
        String value = values.get(key);
        if (value == null || value.trim().isEmpty()) {
            throw new IllegalArgumentException("Missing --" + key);
        }
        return Paths.get(value);
    }

    private static boolean accepted(String claim) {
        return SAT_CANDIDATE.equals(claim) || UNSAT_CLOSED.equals(claim);
    }

    /**
     * What the plan recorded at each symbolized port.
     *
     * <p>Every {@code symbolize} row in the runtime plan carries the {@code
     * primitiveValue} the call returned and the {@code siteId} it returned it
     * at.  The Composer copies both into the manifest's recorded-root ledger,
     * but only for ports whose manual root it managed to name, so a manifest
     * can carry a Boolean root with no recorded value while the plan that
     * produced it says plainly that the call returned {@code false}.  A gate
     * that reads only the manifest then has to guess the recorded polarity,
     * and guessing it inverts every statement about which marker is the
     * mechanism.</p>
     *
     * <p>This used to also carry the experiment's declared wire flows and the
     * regions the plan bound each one's ports to, so a report could say how
     * many flows exist and which regions they were expected to join.  Nothing
     * decided anything on them -- whether a flow is realized is decided by
     * whether the composition lowered a boundary value into a term -- and a
     * wire flow is runtime attach, published by the replay that made it.</p>
     */
    public static final class PlannedSymbolicRoots {
        private final Map<String, JsonObject> plannedRoots;

        private PlannedSymbolicRoots(Map<String, JsonObject> plannedRoots) {
            this.plannedRoots = plannedRoots;
        }

        /** The plan's own row for this symbolized port, or null. */
        JsonObject plannedRoot(String portId) {
            return portId == null ? null : plannedRoots.get(portId);
        }

        /** No plan to read, so no port has a recorded value. */
        public static PlannedSymbolicRoots none() {
            return new PlannedSymbolicRoots(
                    new LinkedHashMap<String, JsonObject>());
        }

        /** Reads every symbolized port the runtime plan records a value for. */
        public static PlannedSymbolicRoots read(String plan)
                throws IOException {
            Map<String, JsonObject> planned = new LinkedHashMap<>();
            if (plan != null && !plan.trim().isEmpty()
                    && Files.isRegularFile(Paths.get(plan.trim()))) {
                for (JsonObject row : ArtifactIO.readJsonl(
                        Paths.get(plan.trim()))) {
                    collectSymbolizedRoots(row, planned);
                }
            }
            return new PlannedSymbolicRoots(planned);
        }

        private static void collectSymbolizedRoots(
                JsonObject plan, Map<String, JsonObject> planned) {
            for (JsonElement goal : array(plan, "closureGoals")) {
                if (!goal.isJsonObject()) {
                    continue;
                }
                for (JsonElement encoded
                        : array(goal.getAsJsonObject(), "symbolize")) {
                    if (!encoded.isJsonObject()) {
                        continue;
                    }
                    JsonObject row = encoded.getAsJsonObject();
                    String port = optionalString(row, "portId");
                    if (port.isEmpty()
                            || optionalString(row, "primitiveValue")
                                    .isEmpty()) {
                        continue;
                    }
                    planned.putIfAbsent(port, row);
                }
            }
        }



    }





    /**
     * A node as every identity in the composition spells it:
     * {@code <instance>/<node>#epoch<n>}, the prefix of an occurrence id and
     * of a location key alike.
     */
    private static final Pattern SOURCE_KEY = Pattern.compile(
            "[A-Za-z0-9_.+-]+/[A-Za-z0-9_.+-]+#epoch[0-9]+");

    /**
     * Every region identity the composition drew a case, a read or a witness
     * from. Region ids appear inside occurrence ids, case owners and location
     * keys as well as in their own field, so they are read as identities
     * rather than from one place.
     */
    static Set<String> realizedRegions(JsonObject manifest) {
        Set<String> regions = new LinkedHashSet<>();
        Matcher matcher = REGION_ID.matcher(
                manifest == null ? "" : manifest.toString());
        while (matcher.find()) {
            regions.add(matcher.group());
        }
        return regions;
    }


    /**
     * How many consumer boundary families the composition realized, from the
     * {@code casePathConditionDependencies} rows the Composer publishes.
     */
    static int consumerBoundaryFamilies(JsonObject manifest) {
        Set<String> families = new LinkedHashSet<>();
        int unnamed = 0;
        for (JsonElement element
                : array(manifest, "casePathConditionDependencies")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject row = element.getAsJsonObject();
            if (!CONSUMER_BOUNDARY_KIND.equals(optionalString(row, "kind"))) {
                continue;
            }
            String family = optionalString(row, "familyKey");
            if (family.isEmpty()) {
                unnamed++;
            } else {
                families.add(family);
            }
        }
        return families.size() + unnamed;
    }

    /** How many arms those consumer boundary families carry in total. */
    static int consumerBoundaryArms(JsonObject manifest) {
        int arms = 0;
        for (JsonElement element
                : array(manifest, "casePathConditionDependencies")) {
            if (element.isJsonObject()
                    && CONSUMER_BOUNDARY_KIND.equals(optionalString(
                            element.getAsJsonObject(), "kind"))) {
                arms += array(element.getAsJsonObject(), "arms").size();
            }
        }
        return arms;
    }




    /**
     * What the probe actually perturbed, so a reader can see which root the
     * root-space verdict rests on.
     *
     * <p>{@code constrainsRootSpace} says some root decides the target; it
     * does not say which, and a run that injects a fault marker cares very
     * much whether the answer is the marker or a wall clock three nodes away.
     */
    static JsonObject probedRoot(JsonObject reach) {
        JsonObject probe = object(reach, "existentialRootProbe");
        JsonObject result = new JsonObject();
        JsonObject rejected = null;
        int solved = 0;
        for (JsonElement element : array(probe, "perturbations")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject row = element.getAsJsonObject();
            if (!optionalString(row, "rejectedBy").isEmpty()) {
                continue;
            }
            solved++;
            if (rejected == null && "unsat".equals(optionalString(row,
                    "status"))) {
                rejected = row;
            }
        }
        result.addProperty("solvedPerturbations", solved);
        result.addProperty("rejected", rejected != null);
        if (rejected != null) {
            result.addProperty("sourceIdentity",
                    optionalString(rejected, "sourceIdentity"));
            result.addProperty("portId", optionalString(rejected, "portId"));
            result.addProperty("occurrenceId",
                    optionalString(rejected, "occurrenceId"));
            result.addProperty("javaTypeDescriptor",
                    optionalString(rejected, "javaTypeDescriptor"));
            result.addProperty("witnessValue",
                    optionalString(rejected, "witnessValue"));
            result.addProperty("perturbedValue",
                    optionalString(rejected, "perturbedValue"));
        }
        return result;
    }

    /**
     * One declared Boolean root, with the polarity it recorded.
     *
     * <p>The marker list is the reach report's {@code roots.booleanInputs} and
     * its order is the order of every valuation's {@code values} vector, so the
     * index is what ties an assignment to a marker. The recorded polarity is
     * <em>observed</em>: it comes from the manifest -- the
     * {@code recordedRootValues} ledger first, and a configured source's own
     * materialization row after it -- and from the runtime plan's
     * {@code symbolize} row, each of which states what the field or port
     * actually held at the mint the recording made.</p>
     *
     * <p>Where nothing states one there is no polarity. Nothing is assumed:
     * {@code stated} is false, no {@code recordedPolarity} and no
     * {@code flipped} is published, and {@link #RECORDED_ROOT_VALUE_UNSTATED}
     * withholds the claim. The default this replaced -- unstated reads as
     * {@code true} -- is what produced HDFS-17960's accepted finding. Its
     * configured source is {@code snapshot.deletion.ordered}, and
     * {@code TestOrderedSnapshotDeletion} sets that flag to {@code false}
     * before the restart the whole composition replays, so the epoch-1
     * recorded value is {@code false} and the satisfying witness at
     * {@code false} reproduces the recorded failure. Against the default it
     * read as a flip, and the run published "a symbolic root flips it" over
     * an empty mechanism list.</p>
     *
     * <p>Two sources that state different values are not a value to pick
     * between and not an absence either: {@code conflict} names both, and
     * {@link #RECORDED_ROOT_VALUE_DISAGREEMENT} withholds the claim under a
     * blocker that prints them.</p>
     */
    static final class Marker {
        private final int index;
        private final String inputKind;
        private final String sourceIdentity;
        private final String portId;
        private final String occurrenceId;
        private final String solverTerm;
        private final String siteId;
        private final String recordedValue;
        private final String conflict;
        private final boolean recordedPolarity;
        private final boolean stated;

        Marker(int index, JsonObject row, String recordedValue,
               String siteId) {
            this(index, row, recordedValue, siteId, "");
        }

        Marker(int index, JsonObject row, String recordedValue,
               String siteId, String conflict) {
            this.index = index;
            this.inputKind = optionalString(row, "inputKind");
            // A configured source carries no sourceIdentity and no portId:
            // it is named by the field it reads and the activation that read
            // it. Falling back to them is what keeps a finding about 17960
            // saying "snapshotDeletionOrdered" rather than an SMT term.
            this.sourceIdentity = firstNonEmpty(
                    optionalString(row, "sourceIdentity"),
                    optionalString(row, "sourceId"));
            this.portId = optionalString(row, "portId");
            this.occurrenceId = firstNonEmpty(
                    optionalString(row, "occurrenceId"),
                    optionalString(row, "sourceOccurrenceId"));
            this.solverTerm = optionalString(row, "solverTerm");
            this.siteId = firstNonEmpty(siteId == null ? "" : siteId,
                    optionalString(row, "fieldSignature"));
            this.conflict = conflict == null ? "" : conflict;
            this.recordedValue = recordedValue == null ? "" : recordedValue;
            // Observed, or absent. A disagreement is not an observation
            // either: two sources naming different values state no polarity
            // for this root, and say so under their own blocker.
            this.stated = !this.recordedValue.isEmpty()
                    && this.conflict.isEmpty();
            this.recordedPolarity = stated
                    && !"false".equals(this.recordedValue);
        }

        /** Whether a recorded value was observed for this root. */
        boolean stated() {
            return stated;
        }

        /** The values disagreeing sources stated, or "" where none do. */
        String conflict() {
            return conflict;
        }

        /**
         * Whether the experiment planted this root or only read it.
         *
         * <p>A {@code REGION_SYMBOLIC_INPUT} is a manual symbolization the
         * task plan asked for: the campaign's hypothesis is that moving it
         * off what it recorded reaches the target, so the buggy polarity is
         * a flip and an accepted claim has to show one. A
         * {@code CONFIGURED_SOURCE_FIELD} is the program's own configuration
         * field, which the recording read and nobody injected; the claim it
         * carries is about the value the recording had, and demanding a flip
         * of it refuses the run for reproducing its own recorded failure.
         * </p>
         */
        boolean planted() {
            return "REGION_SYMBOLIC_INPUT".equals(inputKind);
        }

        /** How a blocker or a finding names this marker. */
        String name() {
            return firstNonEmpty(sourceIdentity, solverTerm);
        }

        /** Where it sits, for a reader following the chain. */
        String where() {
            String at = firstNonEmpty(siteId, portId);
            String occurrence = occurrenceId.isEmpty() ? ""
                    : " at " + occurrenceId;
            return at.isEmpty() ? occurrence.trim()
                    : (occurrence.isEmpty() ? at : at + occurrence);
        }

        /** This marker's assignment under one valuation, or null. */
        JsonObject assignment(JsonObject valuation) {
            JsonArray values = array(valuation, "values");
            if (index >= values.size()
                    || !values.get(index).isJsonPrimitive()) {
                return null;
            }
            boolean value = values.get(index).getAsBoolean();
            JsonObject row = new JsonObject();
            row.addProperty("markerIndex", index);
            row.addProperty("sourceIdentity", sourceIdentity);
            row.addProperty("portId", portId);
            row.addProperty("occurrenceId", occurrenceId);
            row.addProperty("siteId", siteId);
            row.addProperty("solverTerm", solverTerm);
            row.addProperty("recordedPolarityStated", stated);
            row.addProperty("value", value);
            // A flip is a comparison, so it exists only where there is
            // something to compare against. An unstated or disputed root
            // publishes neither polarity nor flip: a reader that defaults
            // either one is doing what this class stopped doing.
            if (stated) {
                row.addProperty("recordedPolarity", recordedPolarity);
                row.addProperty("recordedValue", recordedValue);
                row.addProperty("flipped", value != recordedPolarity);
            } else if (!conflict.isEmpty()) {
                row.addProperty("recordedValueConflict", conflict);
            }
            return row;
        }
    }

    /**
     * Every declared fault marker, in valuation-vector order.
     *
     * <p>{@code siteId} is carried across from the recorded-root ledger where
     * the manifest has one: a reader chasing "which call was made to fail"
     * wants the call site, and the reach report's root row carries only the
     * port.</p>
     */
    static List<Marker> declaredMarkers(JsonObject manifest,
                                        JsonObject reach) {
        return declaredMarkers(manifest, reach, PlannedSymbolicRoots.none());
    }

    /**
     * Every declared fault marker, in valuation-vector order, with the
     * recorded value every source that observed one states.
     *
     * <p>Three sources observe a root's concrete value at the mint that
     * made it symbolic, and all three are read rather than ranked. The
     * {@code recordedRootValues} ledger is the composer's own roll-up. A
     * configured source's materialization row carries what the VM read out
     * of the field before it symbolized it -- a configured source has no
     * port and no {@code symbolize} row, so on a manifest composed before
     * the ledger absorbed configured sources it is the only statement there
     * is. The runtime plan's {@code symbolize} row carries the
     * {@code primitiveValue} the recording saw at a manual port.</p>
     *
     * <p>Where they agree there is one observation. Where they disagree
     * there is none: the marker carries both values and
     * {@link #RECORDED_ROOT_VALUE_DISAGREEMENT} withholds the claim naming
     * them. Dropping the disagreement to "unstated" -- which is what
     * {@code mergeRecordedSourceValue} used to do one layer up -- turned a
     * contradiction into an absence, and the absence then defaulted.</p>
     */
    static List<Marker> declaredMarkers(JsonObject manifest,
                                        JsonObject reach,
                                        PlannedSymbolicRoots flows) {
        // Per root: every distinct value some source observed, in the order
        // the sources were read, each tagged with the source that said it.
        Map<String, Map<String, String>> observed = new LinkedHashMap<>();
        Map<String, String> sites = new LinkedHashMap<>();
        for (JsonElement element
                : array(manifest, ComposedManifest.RECORDED_ROOT_VALUES)) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject ledger = element.getAsJsonObject();
            String term = optionalString(ledger, "solverTerm");
            observe(observed, term, optionalString(ledger, "recordedValue"),
                    ComposedManifest.RECORDED_ROOT_VALUES);
            // A ledger row the composer already found two readings for
            // states the disagreement rather than a value.
            observeAll(observed, term, optionalString(ledger,
                    ComposedManifest.RECORDED_VALUE_CONFLICT),
                    ComposedManifest.RECORDED_ROOT_VALUES);
            if (!term.isEmpty()) {
                sites.put(term, optionalString(ledger, "siteId"));
            }
        }
        for (JsonElement element : array(manifest, ComposedManifest
                .CONFIGURED_SOURCE_MATERIALIZATION_FIELD)) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject source = element.getAsJsonObject();
            String term = optionalString(source, "solverTerm");
            observe(observed, term, optionalString(source,
                    ComposedManifest.RECORDED_SOURCE_VALUE),
                    ComposedManifest.CONFIGURED_SOURCE_MATERIALIZATION_FIELD);
            observeAll(observed, term, optionalString(source,
                    ComposedManifest.RECORDED_VALUE_CONFLICT),
                    ComposedManifest.CONFIGURED_SOURCE_MATERIALIZATION_FIELD);
            if (!term.isEmpty()) {
                sites.put(term, firstNonEmpty(sites.get(term),
                        optionalString(source, "fieldSignature")));
            }
        }
        List<Marker> markers = new ArrayList<>();
        JsonArray rows = array(object(reach, "roots"), "booleanInputs");
        for (int index = 0; index < rows.size(); index++) {
            if (!rows.get(index).isJsonObject()) {
                continue;
            }
            JsonObject row = rows.get(index).getAsJsonObject();
            String term = optionalString(row, "solverTerm");
            String site = sites.get(term);
            // The plan that produced the manifest observed the port too.
            JsonObject planned = flows == null ? null
                    : flows.plannedRoot(optionalString(row, "portId"));
            if (planned != null) {
                observe(observed, term,
                        optionalString(planned, "primitiveValue"),
                        "runtimePlan.symbolize");
                site = firstNonEmpty(site, optionalString(planned, "siteId"));
            }
            Map<String, String> readings = observed.get(term);
            String value = readings == null || readings.isEmpty() ? ""
                    : readings.keySet().iterator().next();
            String conflict = readings == null || readings.size() < 2 ? ""
                    : namedReadings(readings);
            markers.add(new Marker(index, row, value, site, conflict));
        }
        return markers;
    }

    /** One source's reading of one root, where it states one. */
    private static void observe(Map<String, Map<String, String>> observed,
                                String term, String value, String source) {
        if (term == null || term.isEmpty() || value == null
                || value.isEmpty()) {
            return;
        }
        Map<String, String> readings = observed.get(term);
        if (readings == null) {
            readings = new LinkedHashMap<>();
            observed.put(term, readings);
        }
        String held = readings.get(value);
        // One source may state the same reading twice -- a ledger row that
        // carries both a value and a conflict list including it. Naming it
        // once is what makes the printed detail readable.
        readings.put(value, held == null ? source
                : held.contains(source) ? held : held + "+" + source);
    }

    /**
     * Every reading a composer-side conflict row already holds.
     *
     * <p>{@link ComposedManifest#RECORDED_VALUE_CONFLICT} is the list of
     * values two mints of one source disagreed on, comma separated. Read as
     * one string it would print as a single made-up value.</p>
     */
    private static void observeAll(Map<String, Map<String, String>> observed,
                                   String term, String values,
                                   String source) {
        if (values == null || values.isEmpty()) {
            return;
        }
        for (String value : values.split(",")) {
            observe(observed, term, value.trim(), source);
        }
    }

    /** {@code false (recordedRootValues), true (runtimePlan.symbolize)}. */
    private static String namedReadings(Map<String, String> readings) {
        List<String> named = new ArrayList<>();
        for (Map.Entry<String, String> reading : readings.entrySet()) {
            named.add(reading.getKey() + " (" + reading.getValue() + ")");
        }
        return String.join(", ", named);
    }

    /** Every marker's assignment under one valuation. */
    static JsonArray markerAssignment(JsonObject valuation,
                                      List<Marker> markers) {
        JsonArray rows = new JsonArray();
        if (valuation == null) {
            return rows;
        }
        for (Marker marker : markers) {
            JsonObject row = marker.assignment(valuation);
            if (row != null) {
                rows.add(row);
            }
        }
        return rows;
    }

    /** The markers this valuation moved off what they recorded. */
    private static List<Marker> flippedMarkers(JsonObject valuation,
                                               List<Marker> markers) {
        List<Marker> flipped = new ArrayList<>();
        if (valuation == null) {
            return flipped;
        }
        for (Marker marker : markers) {
            JsonObject row = marker.assignment(valuation);
            if (row != null && optionalBool(row, "flipped", false)) {
                flipped.add(marker);
            }
        }
        return flipped;
    }

    /**
     * Whether the recording is itself the failing run, root-determined.
     *
     * <p>The shape HDFS-17960 has, and the fourth finding kind: the fatal
     * predicate is satisfied with every declared root left at the value it
     * recorded, and every enumerated valuation that moves one off it is
     * refuted. Nothing was injected and nothing drifted; the recorded
     * configuration is what reaches the target, and the chain shows the
     * roots decide it rather than merely accompany it.</p>
     *
     * <p>Every recorded value has to be stated for this to mean anything --
     * "at the value it recorded" is not a sentence about a root nobody
     * recorded -- and at least one flip has to have been asked, or the
     * absence of a satisfying flip says nothing.</p>
     */
    private static boolean recordedFailureExplained(JsonArray valuations,
                                                    List<Marker> markers) {
        if (markers.isEmpty()) {
            return false;
        }
        for (Marker marker : markers) {
            if (!marker.stated()) {
                return false;
            }
        }
        JsonObject atRecorded = allRecordedValuation(valuations, markers);
        if (atRecorded == null || !satisfied(atRecorded)) {
            return false;
        }
        int refutedFlips = 0;
        for (int ordinal = 0; ordinal < valuations.size(); ordinal++) {
            JsonObject candidate = row(valuations, ordinal);
            if (candidate == null
                    || flippedMarkers(candidate, markers).isEmpty()) {
                continue;
            }
            if (!decided(candidate) || satisfied(candidate)) {
                // A flip that reaches the target, or one the solver never
                // answered, leaves the question open either way.
                return false;
            }
            refutedFlips++;
        }
        return refutedFlips > 0;
    }

    /**
     * The valuation that leaves every marker at what it recorded: the world
     * as the recording had it, and the only well-defined "other" polarity
     * once more than one marker exists.
     */
    private static JsonObject allRecordedValuation(JsonArray valuations,
                                                   List<Marker> markers) {
        for (int ordinal = 0; ordinal < valuations.size(); ordinal++) {
            JsonObject candidate = row(valuations, ordinal);
            if (candidate == null) {
                continue;
            }
            if (flippedMarkers(candidate, markers).isEmpty()
                    && array(candidate, "values").size() >= markers.size()) {
                return candidate;
            }
        }
        return null;
    }

    /**
     * Whether the injected fault marker is what decides the target.
     *
     * <p>An experiment that injects a marker states a hypothesis: with the
     * fault the target is reached, without it the target is not. The formula
     * answers that in one way only -- the marker's two polarities disagree on
     * satisfiability. Both polarities satisfiable therefore means the marker
     * did not decide the target, and that is what this evidence records.</p>
     *
     * <p>It is not by itself a refusal. Under the acceptance ruling a witness
     * in the polarity that has no fault is a real finding whenever every
     * mechanism it names is one the world does -- drift inside the recorded
     * clock window included, boundary values included, since the window is the
     * recording's statement about what that clock could have read and a value
     * on it is inside it. Whether this row blocks is decided by
     * {@link WitnessLegitimacy}: it blocks while some satisfying witness rests
     * on freedom nobody accounted for, and is reported as a finding otherwise.
     * </p>
     *
     * <p>The {@code mechanismNecessity} probe stays beside it as evidence a
     * reader may weigh -- a mechanism the polarity survives without carried
     * less than one it cannot do without -- and decides nothing on its own.
     * The census of how many named mechanisms sit inside the window is kept
     * for the same reason.</p>
     */
    static JsonObject faultMarkerEvidence(JsonObject manifest,
                                          JsonObject reach,
                                          PlannedSymbolicRoots flows) {
        List<Marker> markers = declaredMarkers(manifest, reach, flows);
        JsonObject evidence = new JsonObject();
        evidence.addProperty("declaredMarkers", markers.size());
        JsonArray rows = new JsonArray();
        evidence.add("markers", rows);
        if (markers.isEmpty()) {
            return evidence;
        }
        long window = Math.max(0L, ClockRootPhysics.skewOf(manifest));
        JsonArray valuations = array(reach, "valuations");
        // "The other polarity" is the world as recorded, which with two
        // markers is one valuation and not one per marker. Reading it per
        // marker -- the first row that happens to assign this index its
        // recorded value -- answers about whichever sibling marker that row
        // also moved.
        JsonObject atRecorded = allRecordedValuation(valuations, markers);
        JsonArray unsaturated = unsaturatedMechanisms(atRecorded, window);
        evidence.addProperty("allRecordedSatisfiable",
                atRecorded != null && satisfied(atRecorded));
        for (Marker marker : markers) {
            JsonObject row = new JsonObject();
            row.addProperty("sourceIdentity", marker.sourceIdentity);
            row.addProperty("portId", marker.portId);
            row.addProperty("occurrenceId", marker.occurrenceId);
            row.addProperty("siteId", marker.siteId);
            row.addProperty("recordedPolarityStated", marker.stated);
            // Observed or absent, here as on every assignment row: a marker
            // evidence block that states a polarity nobody recorded is the
            // same invention one layer up.
            if (marker.stated) {
                row.addProperty("recordedPolarity", marker.recordedPolarity);
                row.addProperty("recordedValue", marker.recordedValue);
            } else if (!marker.conflict.isEmpty()) {
                row.addProperty("recordedValueConflict", marker.conflict);
            }
            // Every enumerated valuation that moves this marker, whatever its
            // siblings do: that is the whole evidence about this marker.
            int flippedRows = 0;
            int flippedSat = 0;
            int flippedUnsat = 0;
            for (int ordinal = 0; ordinal < valuations.size(); ordinal++) {
                JsonObject candidate = row(valuations, ordinal);
                JsonObject assigned = candidate == null ? null
                        : marker.assignment(candidate);
                if (assigned == null
                        || !optionalBool(assigned, "flipped", false)) {
                    continue;
                }
                flippedRows++;
                if (satisfied(candidate)) {
                    flippedSat++;
                } else if (decided(candidate)) {
                    flippedUnsat++;
                }
            }
            row.addProperty("flippedValuations", flippedRows);
            row.addProperty("flippedSatisfiable", flippedSat);
            row.addProperty("flippedUnsatisfiable", flippedUnsat);
            boolean recordedSat = atRecorded != null
                    && satisfied(atRecorded);
            boolean recordedDecided = atRecorded != null
                    && decided(atRecorded);
            row.addProperty("recordedPolaritySatisfiable", recordedSat);
            row.addProperty("flippedPolaritySatisfiable", flippedSat > 0);
            // Every refuted flip was refuted, and the other polarity was
            // answered: this marker decides the target predicate. Which of
            // its two values reaches the target is a separate fact -- a
            // planted fault decides it by being flipped, a configuration
            // field the recording already held decides it by staying put --
            // and reading only the first is what made HDFS-17960's recorded
            // false look like a counterfactual. An undecided row answers
            // neither, so a timeout leaves the question open.
            boolean decides = flippedSat > 0
                    ? recordedDecided && !recordedSat
                    : recordedSat && flippedRows > 0
                            && flippedUnsat == flippedRows;
            // Not the mechanism: every way of moving this marker was refuted
            // and its recorded value reaches nothing either, so no polarity
            // of it is what reached the target.
            row.addProperty(NOT_A_MECHANISM.toLowerCase(java.util.Locale.ROOT),
                    flippedRows > 0 && flippedSat == 0
                            && flippedUnsat == flippedRows && !decides);
            boolean flips = flippedSat > 0 && recordedDecided && !recordedSat;
            JsonArray necessary = necessaryMechanisms(reach,
                    marker.solverTerm, marker.recordedPolarity);
            row.addProperty("polarityDecides", decides);
            row.addProperty("reachesAtRecordedValue", decides && !flips);
            // A reader deciding whether to trust the mechanism needs to see
            // how much of it is pressed against the window: six interior rows
            // out of ten is a different claim from six out of six.
            row.addProperty("otherPolarityMechanismCount",
                    atRecorded == null ? 0
                            : array(atRecorded, "witnessMechanisms").size());
            row.addProperty("otherPolarityUnsaturatedCount",
                    unsaturated.size());
            row.addProperty("clockWindowMillis", window);
            row.add("otherPolarityMechanisms", unsaturated);
            row.add("necessaryMechanisms", necessary);
            row.addProperty("determining", decides || necessary.size() > 0);
            rows.add(row);
        }
        return evidence;
    }

    /** The findings a marker that is not the mechanism justifies. */
    private static List<JsonObject> notAMechanismFindings(
            JsonObject faultMarkers) {
        List<JsonObject> findings = new ArrayList<>();
        String field = NOT_A_MECHANISM.toLowerCase(java.util.Locale.ROOT);
        for (JsonElement element : array(faultMarkers, "markers")) {
            if (!element.isJsonObject()
                    || !optionalBool(element.getAsJsonObject(), field,
                            false)) {
                continue;
            }
            JsonObject marker = element.getAsJsonObject();
            findings.add(blocker(NOT_A_MECHANISM,
                    optionalString(marker, "sourceIdentity"),
                    "every enumerated valuation that flips this marker is"
                            + " unsatisfiable ("
                            + optionalInteger(marker, "flippedValuations", 0)
                            + " of them), so failing "
                            + firstNonEmpty(optionalString(marker, "siteId"),
                                    optionalString(marker, "portId"))
                            + " at " + optionalString(marker, "occurrenceId")
                            + " does not reach the target: this marker is not"
                            + " the mechanism, and the run does not rest on"
                            + " it"));
        }
        return findings;
    }

    /**
     * The named mechanisms the solver showed this polarity cannot do without.
     *
     * <p>Each row is one extra query the extractor already ran: the polarity
     * asserted, the mechanism's roots pinned to their recorded values. An
     * {@code unsat} there is the only evidence that the mechanism carried the
     * polarity rather than merely accompanying it.</p>
     */
    private static JsonArray necessaryMechanisms(JsonObject reach,
                                                 String markerTerm,
                                                 boolean polarity) {
        JsonArray necessary = new JsonArray();
        JsonObject probe = object(reach,
                BooleanReachConditionExtractor.MECHANISM_NECESSITY);
        for (JsonElement element : array(probe, "mechanisms")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject row = element.getAsJsonObject();
            if (optionalBool(row, "necessary", false)
                    && optionalBool(row, "polarity", false) == polarity
                    && optionalString(row, "marker").equals(markerTerm)) {
                necessary.add(row);
            }
        }
        return necessary;
    }

    /**
     * Mechanism rows that name something the recording leaves room for.
     *
     * <p>"Inside the window" is inclusive of its bound, which is the same
     * reading {@link WitnessLegitimacy} decides legitimacy by: the window is
     * the recording's own statement of what that clock could have read, so a
     * value on it is a value it could have read. The two must agree or the
     * census beside a marker row would contradict the verdict above it.</p>
     */
    private static JsonArray unsaturatedMechanisms(JsonObject valuation,
                                                   long window) {
        JsonArray named = new JsonArray();
        if (valuation == null || !satisfied(valuation)) {
            return named;
        }
        for (JsonElement element : array(valuation, "witnessMechanisms")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject mechanism = element.getAsJsonObject();
            String kind = optionalString(mechanism, "kind");
            if (kind.isEmpty() || "MARKER_FLIPPED".equals(kind)) {
                continue;
            }
            if (mechanism.has("skewMillis")) {
                long skew = Math.abs(optionalLongInteger(mechanism,
                        "skewMillis", 0L));
                if (skew > window) {
                    continue;
                }
            }
            named.add(mechanism);
        }
        return named;
    }

    /**
     * The finding a non-determining marker justifies, or null.
     *
     * <p>Both polarities satisfiable is a finding and not by itself a refusal:
     * the acceptance ruling is that a witness in the polarity without the
     * fault is a real thing about the program when everything it names is
     * something the world does. What decides whether this row is a blocker is
     * therefore not the polarity count but whether any satisfying witness
     * rested on freedom nobody accounted for -- the caller passes that in as
     * {@code freedom}, and an empty {@code freedom} makes this a finding.</p>
     */
    private static JsonObject faultMarkerBlocker(JsonObject evidence,
                                                 String freedom) {
        List<String> undetermined = new ArrayList<>();
        List<String> detail = new ArrayList<>();
        for (JsonElement element : array(evidence, "markers")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject marker = element.getAsJsonObject();
            if (optionalBool(marker, "determining", false)) {
                continue;
            }
            undetermined.add(optionalString(marker, "sourceIdentity"));
            detail.add(optionalString(marker, "portId")
                    + ": recorded polarity "
                    + (optionalBool(marker, "recordedPolaritySatisfiable",
                            false) ? "sat" : "unsat")
                    + ", flipped polarity "
                    + (optionalBool(marker, "flippedPolaritySatisfiable",
                            false) ? "sat" : "unsat")
                    + ", "
                    + array(marker, "necessaryMechanisms").size()
                    + " necessary mechanism(s) of "
                    + optionalInteger(marker, "otherPolarityMechanismCount",
                            0)
                    + " named ("
                    + optionalInteger(marker,
                            "otherPolarityUnsaturatedCount", 0)
                    + " inside the recorded window)");
        }
        if (undetermined.isEmpty()) {
            return null;
        }
        return blocker(FAULT_MARKER_NOT_DETERMINING,
                String.join(",", undetermined),
                "no polarity of " + undetermined.size()
                        + " declared fault marker(s) was shown to decide the"
                        + " target"
                        + (freedom == null || freedom.isEmpty()
                                ? " and the polarity without the fault is a"
                                + " witness this composition explains, so"
                                + " this is a finding: "
                                : " and a satisfying witness rests on"
                                + " unexplained freedom (" + freedom + "): ")
                        + String.join("; ", detail));
    }

    /**
     * Reads every enumerated valuation against the mechanisms the world
     * allows, and says what is left over.
     *
     * <p>The result carries one row per valuation -- the finding a reader
     * puts in a report -- plus the three summaries the decision needs: whether
     * any satisfying witness was left unexplained, which freedoms those were,
     * and which of them live in the witness itself rather than in a gap the
     * composition already publishes under a blocker of its own.</p>
     *
     * <p>The buggy polarity is <em>some</em> enumerated valuation that moves
     * at least one marker off what it recorded, is satisfiable, and is
     * explained. It is not "every marker flipped", and it is not one fixed
     * marker: an experiment may plant several and they need not all be the
     * bug. hdfs-17899-bug1 plants two on the Balancer, and flipping the
     * constructor's {@code updateBlockKeys} at occurrence #1 aborts the test,
     * so demanding a witness there would refuse a run whose actual mechanism
     * is the other marker -- the {@code BlockKeyUpdater} thread's periodic
     * {@code getBlockKeys} at occurrence #5, whose catch is the path
     * production tolerates. The "other" polarity is correspondingly the one
     * valuation that leaves every marker as recorded.</p>
     *
     * <p>That demand is made of <em>planted</em> markers only. A manual
     * symbolization is the experiment's own hypothesis, so its buggy polarity
     * is a flip and an accepted claim has to show one. A configured source is
     * the program's own configuration field, which the recording read and
     * nobody injected: the claim it carries is about the value the recording
     * had. HDFS-17960 is that case -- {@code snapshot.deletion.ordered} is
     * recorded {@code false} on the epoch-1 NameNode the whole composition
     * replays, and the satisfying witness at {@code false} reproduces the
     * recorded failure. Demanding a flip there refuses a run for reproducing
     * its own recording, and defaulting the unstated polarity to {@code true}
     * hid that by reporting the reproduction as a flip. A run with no planted
     * marker therefore asks only that some satisfying witness be explained --
     * the same question the clock cases ask.</p>
     */
    private static JsonObject witnessLegitimacy(
            JsonObject manifest, JsonObject reach, JsonArray valuations,
            String degeneracy,
            List<String> unrealizedFlows, PlannedSymbolicRoots flows) {
        long window = Math.max(0L, ClockRootPhysics.skewOf(manifest));
        List<WitnessLegitimacy.Freedom> composition =
                WitnessLegitimacy.compositionFreedoms(degeneracy);
        List<Marker> markers = declaredMarkers(manifest, reach, flows);
        List<Marker> planted = new ArrayList<>();
        for (Marker marker : markers) {
            if (marker.planted()) {
                planted.add(marker);
            }
        }
        boolean recordedFailure = recordedFailureExplained(valuations,
                markers);
        // What the necessity probe said about each valuation's clock group.
        Map<Integer, WitnessLegitimacy.ClockNecessity> clockNecessity =
                clockNecessityByValuation(reach);
        boolean anyClockNecessary = clockNecessity.containsValue(
                WitnessLegitimacy.ClockNecessity.NECESSARY);
        JsonArray findings = new JsonArray();
        Set<String> freedoms = new LinkedHashSet<>();
        Set<String> witnessLocal = new LinkedHashSet<>();
        boolean someSatUnexplained = false;
        boolean someSatWitnessExplained = false;
        // Some valuation moved a marker, was satisfiable, and was explained:
        // that is the buggy polarity, whichever marker it moved.
        boolean flippedWitnessAccepted = false;
        int acceptedOrdinal = -1;
        // The first explained satisfying witness, whatever it moved: what a
        // run with no planted marker rests on.
        int explainedOrdinal = -1;
        // Per valuation: satisfied, and free of the freedom that lives in the
        // witness itself. Composition freedoms are excluded here because each
        // already withholds acceptance under its own blocker, and asking the
        // buggy polarity to answer for them too would name one fact twice.
        List<Boolean> witnessExplained = new ArrayList<>();
        for (int index = 0; index < valuations.size(); index++) {
            JsonObject candidate = row(valuations, index);
            JsonArray assignment = markerAssignment(candidate, markers);
            JsonObject finding = WitnessLegitimacy.classify(candidate, index,
                    window, composition, assignment,
                    clockNecessity.getOrDefault(index,
                            WitnessLegitimacy.ClockNecessity.UNKNOWN),
                    recordedFailure);
            findings.add(finding);
            Set<String> local = new LinkedHashSet<>();
            for (JsonElement element : array(finding, "freedoms")) {
                if (!element.isJsonObject()) {
                    continue;
                }
                String code = optionalString(element.getAsJsonObject(),
                        "code");
                if (witnessLocal(code)) {
                    local.add(code);
                }
            }
            boolean satisfying = candidate != null && satisfied(candidate);
            witnessExplained.add(satisfying && local.isEmpty());
            if (!satisfying) {
                continue;
            }
            if (local.isEmpty()) {
                someSatWitnessExplained = true;
                if (explainedOrdinal < 0) {
                    explainedOrdinal = index;
                }
                if (!flippedMarkers(candidate, planted).isEmpty()) {
                    flippedWitnessAccepted = true;
                    if (acceptedOrdinal < 0) {
                        acceptedOrdinal = index;
                    }
                }
            }
            if (WitnessLegitimacy.UNEXPLAINED.equals(
                    optionalString(finding, "verdict"))) {
                someSatUnexplained = true;
                for (JsonElement element : array(finding, "freedoms")) {
                    if (element.isJsonObject()) {
                        freedoms.add(optionalString(
                                element.getAsJsonObject(), "code"));
                    }
                }
                witnessLocal.addAll(local);
            }
        }
        JsonObject result = new JsonObject();
        result.add("valuations", findings);
        result.addProperty("someSatisfyingWitnessUnexplained",
                someSatUnexplained);
        result.addProperty("freedomCodes", String.join(",", freedoms));
        result.addProperty("witnessLocalFreedomCodes",
                String.join(",", witnessLocal));
        // A clock case declares no marker, so there is no polarity to flip:
        // its whole hypothesis is that a wall clock decided the target. An
        // explained witness is then necessary but not sufficient -- the
        // clock has to have been needed. A satisfying witness that survives
        // every clock going back to what it recorded is a witness the clock
        // played no part in, and accepting it publishes a clock finding the
        // formula does not support.
        boolean clockOnly = planted.isEmpty()
                && !clockNecessity.isEmpty();
        result.addProperty("faultPolarityNotWitnessed",
                planted.isEmpty()
                        ? (someSatWitnessExplained
                                && (!clockOnly || anyClockNecessary) ? ""
                                : clockOnly && !anyClockNecessary
                                ? "no clock decision on the fatal slice is"
                                + " necessary: every satisfying witness"
                                + " survives pinning the clocks to what they"
                                + " recorded" + clockDecisionNote(reach)
                                : "the enumerated valuations")
                        : (flippedWitnessAccepted ? "" : markerNames(planted)));
        result.addProperty("clockMechanismNecessary", anyClockNecessary);
        result.addProperty("clockOnlyExperiment", clockOnly);
        result.add("clockDecisionsOutsideWindow",
                clockDecisionsOutsideWindow(reach));
        result.add("clockDecisionsRefusedWithoutWindow",
                clockDecisionsWithCode(reach, BooleanReachConditionExtractor
                        .CLOCK_DECISION_REFUSED_WITHOUT_WINDOW));
        // Which valuation the acceptance rests on, so a probe can assert that
        // marker assignment rather than guess one.
        // A run with no planted marker rests on the witness it explained,
        // and a probe still needs one valuation to assert.
        int restsOn = acceptedOrdinal >= 0 ? acceptedOrdinal
                : planted.isEmpty() ? explainedOrdinal : -1;
        // The same answer on the row itself.  A consumer reading one witness
        // row can then tell whether the claim rests on it without carrying
        // the ordinal in from another document; every row states it, so an
        // absent flag is an artifact older than this field rather than a
        // row nobody classified.
        for (int index = 0; index < findings.size(); index++) {
            JsonElement finding = findings.get(index);
            if (finding.isJsonObject()) {
                finding.getAsJsonObject().addProperty("accepted",
                        index == restsOn);
            }
        }
        result.addProperty("acceptedValuationOrdinal", restsOn);
        // All three names are claims about recorded values -- moved off one,
        // left at one -- so none of them can be said of a run whose roots
        // nobody recorded. laneX's artifact was published as
        // RECORDED_ROOT_VALUES_REPRODUCED over an empty recorded-root ledger,
        // which reads as "the witness reproduces the recording" about a
        // recording the run never read.
        boolean everyValueStated = !markers.isEmpty();
        for (Marker marker : markers) {
            everyValueStated &= marker.stated();
        }
        result.addProperty("acceptedWitnessKind",
                restsOn < 0 || !everyValueStated ? ""
                : acceptedOrdinal >= 0 ? FLIPPED_PLANTED_MARKER
                : flippedMarkers(row(valuations, restsOn), markers).isEmpty()
                ? RECORDED_ROOT_VALUES_REPRODUCED : UNPLANTED_ROOT_MOVED);
        result.addProperty("declaredMarkers", markers.size());
        result.addProperty("plantedMarkers", planted.size());
        result.addProperty("recordedFailureExplained", recordedFailure);
        // Which of the four shapes the accepted witness is, read off the row
        // itself rather than re-derived: one answer, published once.
        JsonObject acceptedRow = restsOn < 0 ? null
                : findingAt(findings, restsOn);
        result.addProperty(WitnessLegitimacy.FINDING_KIND,
                acceptedRow == null ? ""
                        : optionalString(acceptedRow,
                                WitnessLegitimacy.FINDING_KIND));
        result.addProperty(RECORDED_ROOT_VALUE_UNSTATED,
                markerNames(unstatedMarkers(markers)));
        result.addProperty(RECORDED_ROOT_VALUE_DISAGREEMENT,
                disagreementDetail(markers));
        return result;
    }

    /** The classified row at one valuation ordinal, or null. */
    private static JsonObject findingAt(JsonArray findings, int ordinal) {
        for (JsonElement element : findings) {
            if (element.isJsonObject() && optionalInteger(
                    element.getAsJsonObject(), "valuationOrdinal", -1)
                    == ordinal) {
                return element.getAsJsonObject();
            }
        }
        return null;
    }

    /** Every declared root no source observed a recorded value for. */
    private static List<Marker> unstatedMarkers(List<Marker> markers) {
        List<Marker> unstated = new ArrayList<>();
        for (Marker marker : markers) {
            if (!marker.stated() && marker.conflict().isEmpty()) {
                unstated.add(marker);
            }
        }
        return unstated;
    }

    /** Every declared root whose sources disagree, with both values named. */
    private static String disagreementDetail(List<Marker> markers) {
        List<String> named = new ArrayList<>();
        for (Marker marker : markers) {
            if (marker.conflict().isEmpty()) {
                continue;
            }
            String where = marker.where();
            named.add(marker.name() + (where.isEmpty() ? "" : " (" + where
                    + ")") + " read " + marker.conflict());
        }
        return String.join("; ", named);
    }

    /** Every declared marker, named as a blocker subject names them. */
    private static String markerNames(List<Marker> markers) {
        List<String> names = new ArrayList<>();
        for (Marker marker : markers) {
            names.add(marker.name());
        }
        return String.join(",", names);
    }

    /**
     * Whether this freedom is one no other blocker already names.
     *
     * <p>An unenumerated root space, a selected free initial arm and an
     * unbound wire each have a blocker of their own, so naming them a second
     * time under {@link #WITNESS_FREEDOM_UNEXPLAINED} would report one fact
     * twice. What is left is the freedom that lives in the witness itself.</p>
     */
    private static boolean witnessLocal(String code) {
        return WitnessLegitimacy.CLOCK_OUTSIDE_WINDOW.equals(code)
                || WitnessLegitimacy.ABSURD_CLOCK_VALUE.equals(code)
                || WitnessLegitimacy.UNEXPLAINED_ROOT_MOVE.equals(code)
                || WitnessLegitimacy.CLOCK_NOT_NECESSARY.equals(code)
                || WitnessLegitimacy.CLOCK_NECESSITY_UNKNOWN.equals(code)
                || WitnessLegitimacy.ABSENT_KEY_DEFAULT.equals(code)
                // The composition-level unbound flow has its own blocker;
                // this one is a property of the model, which no other
                // blocker reads, so it belongs to the witness.
                || WitnessLegitimacy.UNBOUND_WIRE_VALUE_TAKEN.equals(code);
    }

    /**
     * The comparisons the solver stage found decidable only beyond the
     * clock window, as the reach report published them.
     */
    private static JsonArray clockDecisionsOutsideWindow(JsonObject reach) {
        return clockDecisionsWithCode(reach, BooleanReachConditionExtractor
                .CLOCK_DECISION_OUTSIDE_WINDOW);
    }

    /** The probed clock comparisons the solver stage gave this code. */
    private static JsonArray clockDecisionsWithCode(JsonObject reach,
                                                    String code) {
        JsonArray rows = new JsonArray();
        for (JsonElement element : array(object(reach,
                BooleanReachConditionExtractor.CLOCK_DECISIONS),
                "decisions")) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            if (code.equals(optionalString(row, "code"))) {
                rows.add(row.deepCopy());
            }
        }
        return rows;
    }

    /**
     * Why the clocks could not have been needed, when the probe knows: the
     * site whose comparison the window decides, and the advance it needs.
     */
    private static String clockDecisionNote(JsonObject reach) {
        JsonObject probe = object(reach,
                BooleanReachConditionExtractor.CLOCK_DECISIONS);
        JsonArray outside = clockDecisionsOutsideWindow(reach);
        String refusedNote = clockDecisionRefusedNote(reach);
        if (outside.size() == 0) return refusedNote;
        StringBuilder note = new StringBuilder("; ")
                .append(outside.size())
                .append(" clock comparison(s) on the slice are decidable")
                .append(" only beyond the +/-")
                .append(optionalLongInteger(probe, "windowMillis", 0L))
                .append("ms window (")
                .append(BooleanReachConditionExtractor
                        .CLOCK_DECISION_OUTSIDE_WINDOW)
                .append("):");
        for (JsonElement element : outside) {
            JsonObject row = element.getAsJsonObject();
            note.append(' ');
            JsonArray sites = array(row, "sites");
            note.append(sites.size() > 0 ? sites.get(0).getAsString()
                    : optionalString(row, "atom"));
            if (row.has("requiredWindowMillisAtMost")) {
                note.append(" needs a window above ")
                        .append(optionalLongInteger(row,
                                "requiredWindowMillisAbove", 0L))
                        .append("ms and at most ")
                        .append(optionalLongInteger(row,
                                "requiredWindowMillisAtMost", 0L))
                        .append("ms");
            } else {
                note.append(" is not admitted by any window up to ")
                        .append(optionalLongInteger(row,
                                "requiredWindowMillisAbove", 0L))
                        .append("ms");
            }
            note.append(';');
        }
        note.append(refusedNote);
        return note.toString();
    }

    /**
     * The comparisons no window admits: asked with the clock left unbounded
     * the blocked polarity is still unsat, so the skew the physics allows is
     * not what refuses it.  What refuses it is the rest of the composition --
     * in practice the recorded case path condition, which replays the
     * observed outcome of the branch the clock decides.  Saying "widen the
     * window" there would send a reader after the wrong thing.
     */
    private static String clockDecisionRefusedNote(JsonObject reach) {
        JsonArray refused = clockDecisionsWithCode(reach,
                BooleanReachConditionExtractor
                        .CLOCK_DECISION_REFUSED_WITHOUT_WINDOW);
        if (refused.size() == 0) return "";
        StringBuilder note = new StringBuilder("; ")
                .append(refused.size())
                .append(" clock comparison(s) on the slice refuse one")
                .append(" polarity with the clock left unbounded, so no")
                .append(" window admits them and the recorded case path")
                .append(" condition is what pins them (")
                .append(BooleanReachConditionExtractor
                        .CLOCK_DECISION_REFUSED_WITHOUT_WINDOW)
                .append("):");
        for (JsonElement element : refused) {
            JsonObject row = element.getAsJsonObject();
            note.append(' ');
            JsonArray sites = array(row, "sites");
            note.append(sites.size() > 0 ? sites.get(0).getAsString()
                    : optionalString(row, "atom"));
            note.append(" has no observed case taking the other branch;");
        }
        return note.toString();
    }

    /**
     * What the reach report's necessity probe said about each valuation's
     * clock group.
     *
     * <p>A row per valuation, and only for the clock mechanism: the probe
     * pins every wall-clock root to its recorded value at once, because
     * "these clocks disagreed" is one claim and asking it one root at a time
     * asks about a skew nobody made.</p>
     */
    private static Map<Integer, WitnessLegitimacy.ClockNecessity>
            clockNecessityByValuation(JsonObject reach) {
        Map<Integer, WitnessLegitimacy.ClockNecessity> result =
                new LinkedHashMap<>();
        JsonObject necessity = object(reach, "mechanismNecessity");
        for (JsonElement element : array(necessity, "mechanisms")) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            if (!WitnessLegitimacy.CLOCK_SKEW.equals(
                    optionalString(row, "mechanism"))) {
                continue;
            }
            int ordinal = optionalInteger(row, "valuationOrdinal", -1);
            if (ordinal < 0) continue;
            WitnessLegitimacy.ClockNecessity verdict =
                    optionalBool(row, "necessary", false)
                            ? WitnessLegitimacy.ClockNecessity.NECESSARY
                            : WitnessLegitimacy.ClockNecessity.NOT_NECESSARY;
            WitnessLegitimacy.ClockNecessity held = result.get(ordinal);
            if (held != WitnessLegitimacy.ClockNecessity.NECESSARY) {
                result.put(ordinal, verdict);
            }
        }
        return result;
    }


    /**
     * Decides the campaign claim from the Composer's manifest and the
     * reach-condition report, and names every blocker that withholds
     * acceptance.
     *
     * @param manifest the composition manifest the Composer published
     * @param reach the reach-condition report the solver stage published
     * @param flows what the experiment declares and where the plan bound it
     */
    public static JsonObject decide(JsonObject manifest, JsonObject reach,
                                    PlannedSymbolicRoots flows) {
        JsonObject reachCondition = object(reach, "reachCondition");
        String reachability = firstNonEmpty(
                optionalString(reachCondition, "reachability"), "UNKNOWN");
        String degeneracy = firstNonEmpty(
                optionalString(reachCondition, "degeneracyCheck"),
                "UNDECIDED");
        boolean unsatClosureComplete = optionalBool(reach,
                ComposedManifest.UNSAT_CLOSURE_COMPLETE, false);
        JsonArray valuations = array(reach, "valuations");
        boolean probeConstrains = optionalBool(
                object(reach, "existentialRootProbe"),
                "constrainsRootSpace", false);
        int boundaryFamilies = consumerBoundaryFamilies(manifest);
        // Whether a declared wire flow was "realized" used to be counted
        // by finding a consumer boundary family the composition had drawn
        // for it, and the value a wire carried was that family's arms.  A
        // wire value is the producer's own expression now: it is realized by
        // arriving, and there is no ledger of families to count it in.
        List<String> unrealizedFlows = Collections.<String>emptyList();

        // Every satisfying witness is read against the mechanisms the world
        // allows before anything is withheld. The acceptance ruling is that a
        // SAT witness is a finding -- in either polarity -- when everything it
        // moved is a marker flip, drift inside the recorded clock window, or a
        // rotation race the recorded write order states; only freedom nobody
        // accounted for blocks.
        JsonObject legitimacy = witnessLegitimacy(manifest, reach, valuations,
                degeneracy, unrealizedFlows, flows);
        boolean someSatUnexplained = optionalBool(legitimacy,
                "someSatisfyingWitnessUnexplained", false);
        String witnessFreedom = optionalString(legitimacy, "freedomCodes");
        String witnessLocalFreedom = optionalString(legitimacy,
                "witnessLocalFreedomCodes");

        List<JsonObject> blockers = new ArrayList<>();

        // The Composer's own refusals and the solver's own gaps are the two
        // sources EMIT aggregates into the campaign gap count. Reading them
        // here keeps this decision and that count derived from one set of
        // facts rather than two.
        String refusals = codes(array(manifest, "finalStatusRefusals"));
        String finalStatus = optionalString(manifest, "finalStatus");
        if (!"FINAL_READY".equals(finalStatus)) {
            blockers.add(blocker(COMPOSER_NOT_FINAL_READY, finalStatus,
                    "the Composer published finalStatus="
                            + firstNonEmpty(finalStatus, "none")
                            + " and refused this composition"));
        }
        // One ledger classes every gap, wherever it was raised.  The
        // composition used to publish four gap arrays this decision never
        // opened -- its own, the bounded-loop model's, the propagation
        // closure's and the fault-control closure's -- so a loop nobody
        // bounded or a read the marker starved could sit inside an accepted
        // formula. GapLedger.blocking() is the same table run_engine.sh
        // partitions gaps.json with, and an unregistered code is blocking in
        // both.
        Set<String> hardGaps = new LinkedHashSet<>();
        for (JsonElement refusal : array(manifest, "finalStatusRefusals")) {
            hardGaps.add("COMPOSE/" + code(refusal));
        }
        collectBlocking(hardGaps, "COMPOSE",
                array(manifest, "gaps"));
        collectBlocking(hardGaps, "COMPOSE",
                array(object(manifest,
                        BoundedLoopComposition.MANIFEST_FIELD), "gaps"));
        collectBlocking(hardGaps, "COMPOSE",
                array(manifest, "symbolicPropagationGaps"));
        collectBlocking(hardGaps, "COMPOSE",
                array(manifest,
                        ComposedManifest.FAULT_CONTROL_GAPS_FIELD));
        collectBlocking(hardGaps, "SOLVE", array(reach, "gaps"));
        if (!hardGaps.isEmpty()) {
            blockers.add(blocker(COMPOSITION_GAPS_UNRESOLVED,
                    String.valueOf(hardGaps.size()),
                    "the selected causal path set has " + hardGaps.size()
                            + " unresolved gap(s): "
                            + String.join(",", hardGaps)));
        }

        // DEGENERATE and UNDECIDED are different findings and were both
        // acceptable to the jq gate that UNDECIDED slipped through. A root
        // space the target provably does not constrain is a refutation of the
        // witness; a root space nobody enumerated is an open question. Each
        // blocks a SAT candidate under its own name.
        if (degeneracy.startsWith("DEGENERATE_")) {
            blockers.add(blocker(DEGENERATE_ROOT_SPACE, degeneracy,
                    "the target predicate is unconstrained by every"
                            + " symbolic root"));
        } else if (degeneracy.startsWith("UNDECIDED_")) {
            blockers.add(blocker(UNDECIDED_ROOT_SPACE, degeneracy,
                    "the degeneracy question was not decided: " + degeneracy));
        }

        // A witness is evidence only if the target predicate depends on a
        // root. Two enumerated valuations that differ in one Boolean root and
        // disagree on satisfiability show that dependence exactly; so does a
        // rejected existential perturbation. Without either, the formula and
        // the roots are disconnected -- but a witness whose every mechanism is
        // one the recording allows says what happened whether or not a root
        // flips it, so this is a blocker only while some satisfying witness is
        // still unexplained.
        boolean unconstrained = "REACHABLE".equals(reachability)
                && !faultSensitive(valuations, probeConstrains);
        if (unconstrained && someSatUnexplained) {
            blockers.add(blocker(TARGET_UNCONSTRAINED_BY_ROOTS,
                    witnessFreedom,
                    "no symbolic root flips the target predicate across the"
                            + " enumerated valuations and a satisfying witness"
                            + " rests on unexplained freedom ("
                            + witnessFreedom + ")"));
        }

        // A declared flow the composition never drew either side of is not
        // in the formula the witness satisfies, whatever the formula then
        // satisfies. Which flows those are is the blocker: a count cannot be
        // acted on, and counting one realization mechanism out of two called
        // a realized flow unrealized.

        // Nothing is compared against a value nobody observed. A declared
        // root whose recorded value no source states, and a root two sources
        // state differently, each withhold the claim under their own name --
        // before any reading of "flipped" or "reproduced" is published from
        // them, because neither reading exists without the observation.
        String unstatedRoots = optionalString(legitimacy,
                RECORDED_ROOT_VALUE_UNSTATED);
        if (!unstatedRoots.isEmpty()) {
            blockers.add(blocker(RECORDED_ROOT_VALUE_UNSTATED, unstatedRoots,
                    "no source states what " + unstatedRoots.split(",").length
                            + " declared root(s) held when the recording"
                            + " symbolized them, so no witness over them is"
                            + " a flip or a reproduction of anything: "
                            + unstatedRoots));
        }
        String disagreeingRoots = optionalString(legitimacy,
                RECORDED_ROOT_VALUE_DISAGREEMENT);
        if (!disagreeingRoots.isEmpty()) {
            blockers.add(blocker(RECORDED_ROOT_VALUE_DISAGREEMENT,
                    disagreeingRoots,
                    "two sources state different recorded values for the same"
                            + " declared root, so the recording contradicts"
                            + " itself about what it held: "
                            + disagreeingRoots));
        }

        // An injected marker is the experiment's own hypothesis, so it is the
        // root the verdict has to rest on. A rejected perturbation of some
        // other root is evidence about that root and no answer about this one.
        JsonObject faultMarkers = faultMarkerEvidence(manifest, reach,
                flows);
        JsonObject markerGap = faultMarkerBlocker(faultMarkers,
                someSatUnexplained ? witnessFreedom : "");
        if (markerGap != null && someSatUnexplained) {
            blockers.add(markerGap);
        }

        // The freedom that lives in the witness itself, rather than in a gap
        // the composition already published under its own blocker.
        if (!witnessLocalFreedom.isEmpty()) {
            blockers.add(blocker(WITNESS_FREEDOM_UNEXPLAINED,
                    witnessLocalFreedom,
                    "a satisfying witness moved a root with no mechanism the"
                            + " recording allows behind it: "
                            + witnessLocalFreedom));
        }

        // The campaign's own hypothesis: some way of moving a declared marker
        // off what it recorded has to have produced a satisfied witness this
        // composition explains. Which marker is not fixed in advance -- an
        // experiment may plant several and only one be the bug.
        String unwitnessedFault = optionalString(legitimacy,
                "faultPolarityNotWitnessed");
        if ("REACHABLE".equals(reachability) && !unwitnessedFault.isEmpty()) {
            blockers.add(blocker(FAULT_POLARITY_NOT_WITNESSED,
                    unwitnessedFault,
                    "no enumerated valuation that flips a declared fault"
                            + " marker off its recorded value is a satisfied"
                            + " witness this composition explains, over "
                            + optionalInteger(legitimacy, "declaredMarkers", 0)
                            + " declared marker(s): " + unwitnessedFault));
        }

        // A reachable verdict is a finding about the program, and a finding
        // names the mechanism it is a finding of. One of the four, on the
        // witness the acceptance rests on, or the run publishes no claim.
        String findingKind = optionalString(legitimacy,
                WitnessLegitimacy.FINDING_KIND);
        if ("REACHABLE".equals(reachability) && findingKind.isEmpty()) {
            blockers.add(blocker(FINDING_MECHANISM_UNNAMED,
                    optionalInteger(legitimacy, "acceptedValuationOrdinal",
                            -1) < 0 ? "NO_ACCEPTED_WITNESS" : "NO_MECHANISM",
                    "no satisfying witness this run would rest on names one"
                            + " of " + WitnessLegitimacy.MARKER_FLIPPED + ", "
                            + WitnessLegitimacy.ROTATION_RACE + ", "
                            + WitnessLegitimacy.CLOCK_SKEW + " or "
                            + WitnessLegitimacy.RECORDED_FAILURE_EXPLAINED
                            + ", so the solver's sat answer is a statement"
                            + " about the formula and not a finding about"
                            + " the program"));
        }

        JsonObject witnessGap = witnessBlocker(valuations, probeConstrains);
        if (witnessGap != null) {
            blockers.add(witnessGap);
        }

        int undecidedRows = undecidedValuations(valuations);
        if (undecidedRows > 0) {
            blockers.add(blocker(SOLVER_UNDECIDED_VALUATIONS,
                    String.valueOf(undecidedRows),
                    "the solver returned neither sat nor unsat on "
                            + undecidedRows + " enumerated valuation(s)"));
        }

        // An unsatisfiable body makes every polarity unsat and every
        // enumerated valuation a restatement of the same contradiction. The
        // reachability answer is then about the composition and not about
        // the target, so it is named here instead of being read as a
        // refutation of the program.
        // Closure is required for a closed refutation and for nothing else:
        // one connected SAT witness stays valid while sibling paths are open.
        if ("UNREACHABLE".equals(reachability) && !unsatClosureComplete) {
            blockers.add(blocker(UNSAT_CLOSURE_INCOMPLETE, "",
                    "the solver reported no valuation but the selected model"
                            + " published no closed path-set authority"));
        }
        if (!"REACHABLE".equals(reachability)
                && !"UNREACHABLE".equals(reachability)) {
            blockers.add(blocker(NO_EXACT_REACHABILITY, reachability,
                    "the solver stage reached no exact reachability"
                            + " decision"));
        }

        String claim = blockers.isEmpty()
                ? ("REACHABLE".equals(reachability)
                        ? SAT_CANDIDATE : UNSAT_CLOSED)
                : INCONCLUSIVE_PARTIAL;

        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", KIND);
        result.addProperty("claim", claim);
        result.addProperty("claimReason", claimReason(claim, reachability,
                blockers, refusals, legitimacy, faultMarkers,
                faultSensitive(valuations, probeConstrains)));
        JsonArray blockerRows = new JsonArray();
        for (JsonObject row : blockers) {
            blockerRows.add(row);
        }
        result.add("blockers", blockerRows);
        result.addProperty("blockerCount", blockers.size());
        result.addProperty("whyNotAccepted", whyNotAccepted(claim, blockers));
        JsonObject rootSpace = new JsonObject();
        rootSpace.addProperty("reachability", reachability);
        rootSpace.addProperty("degeneracyCheck", degeneracy);
        rootSpace.addProperty("faultSensitive",
                faultSensitive(valuations, probeConstrains));
        rootSpace.addProperty("consumerBoundaryFamilies", boundaryFamilies);
        rootSpace.addProperty("consumerBoundaryArms",
                consumerBoundaryArms(manifest));
        rootSpace.addProperty("realizedRegions",
                realizedRegions(manifest).size());
        rootSpace.add("faultMarkers", faultMarkers);
        // Findings the ruling reports rather than blocks: a marker satisfiable
        // in both polarities whose other polarity is explained is one of them,
        // so it is published here instead of vanishing with its blocker.
        JsonArray reportedFindings = new JsonArray();
        if (markerGap != null && !someSatUnexplained) {
            reportedFindings.add(markerGap);
        }
        if (unconstrained && !someSatUnexplained) {
            reportedFindings.add(blocker(TARGET_UNCONSTRAINED_BY_ROOTS, "",
                    "no symbolic root flips the target predicate across the"
                            + " enumerated valuations, and every satisfying"
                            + " witness is explained: a finding about the"
                            + " mechanism rather than about the marker"));
        }
        // A marker every flip of which is unsatisfiable is not the mechanism.
        // That is a statement about the experiment's own hypothesis, and it is
        // published rather than held against the run: hdfs-17899-bug1's
        // constructor marker aborts the test, and the run rests on the other
        // one.
        for (JsonObject row : notAMechanismFindings(faultMarkers)) {
            reportedFindings.add(row);
        }
        for (JsonObject row : uncomposedTargetOccurrences(manifest)) {
            reportedFindings.add(row);
        }
        rootSpace.add("reportedFindings", reportedFindings);
        // Which valuation the acceptance rests on, so a probe asserting the
        // buggy polarity has one marker assignment to assert rather than a
        // guess at which marker the bug is.
        rootSpace.addProperty("acceptedValuationOrdinal",
                optionalInteger(legitimacy, "acceptedValuationOrdinal", -1));
        // Which shape the acceptance has: a planted marker flipped, or every
        // declared root left at what the recording had. A probe asserting the
        // buggy polarity needs to know which of the two it is looking at.
        rootSpace.addProperty("acceptedWitnessKind",
                optionalString(legitimacy, "acceptedWitnessKind"));
        // Which of the four named shapes the acceptance is a finding of, and
        // what the recorded-value ledger left open. A harness reading only
        // result.json gets the mechanism by name here.
        rootSpace.addProperty("acceptedFindingKind",
                optionalString(legitimacy, WitnessLegitimacy.FINDING_KIND));
        rootSpace.addProperty("recordedFailureExplained",
                optionalBool(legitimacy, "recordedFailureExplained", false));
        // Whether this run's whole hypothesis is a clock, and whether the
        // probe found one it needs. Both were decided and then discarded:
        // the necessity map they are computed from was empty on every real
        // run, so "clock only" was never true and "necessary" never asked.
        rootSpace.addProperty("clockOnlyExperiment",
                optionalBool(legitimacy, "clockOnlyExperiment", false));
        rootSpace.addProperty("clockMechanismNecessary",
                optionalBool(legitimacy, "clockMechanismNecessary", false));
        rootSpace.addProperty("unstatedRecordedRootValues",
                optionalString(legitimacy, RECORDED_ROOT_VALUE_UNSTATED));
        rootSpace.addProperty("disagreeingRecordedRootValues",
                optionalString(legitimacy, RECORDED_ROOT_VALUE_DISAGREEMENT));
        rootSpace.addProperty("plantedMarkers",
                optionalInteger(legitimacy, "plantedMarkers", 0));
        result.add(WitnessLegitimacy.FINDINGS,
                legitimacy.getAsJsonArray("valuations"));
        rootSpace.add("probedRoot", probedRoot(reach));
        rootSpace.addProperty(ComposedManifest.UNSAT_CLOSURE_COMPLETE,
                unsatClosureComplete);
        result.add("rootSpace", rootSpace);
        return result;
    }

    /**
     * Whether some symbolic root decides the target predicate. A rejected
     * existential perturbation is the solver's own proof of that; otherwise
     * two enumerated valuations one Boolean root apart must disagree on
     * satisfiability.
     */
    static boolean faultSensitive(JsonArray valuations,
                                  boolean probeConstrains) {
        if (probeConstrains) {
            return true;
        }
        for (int left = 0; left < valuations.size(); left++) {
            JsonObject first = row(valuations, left);
            if (first == null) {
                continue;
            }
            for (int right = left + 1; right < valuations.size(); right++) {
                JsonObject second = row(valuations, right);
                if (second == null) {
                    continue;
                }
                if (!decided(first) || !decided(second)) {
                    continue;
                }
                if (satisfied(first) == satisfied(second)) {
                    continue;
                }
                if (differingRoots(first, second) == 1) {
                    return true;
                }
            }
        }
        return false;
    }

    private static int differingRoots(JsonObject first, JsonObject second) {
        JsonArray left = array(first, "values");
        JsonArray right = array(second, "values");
        if (left.size() != right.size() || left.size() == 0) {
            return -1;
        }
        int differing = 0;
        for (int index = 0; index < left.size(); index++) {
            if (!left.get(index).equals(right.get(index))) {
                differing++;
            }
        }
        return differing;
    }

    /**
     * An existential witness that is every-zero, or identical under every
     * enumerated valuation while no perturbation of it was rejected, is a
     * value the target predicate does not read. It is reported rather than
     * accepted as the witness of a bug.
     */
    private static JsonObject witnessBlocker(JsonArray valuations,
                                             boolean probeConstrains) {
        if (probeConstrains) {
            return null;
        }
        List<String> vectors = new ArrayList<>();
        boolean allZero = true;
        int witnessed = 0;
        for (int index = 0; index < valuations.size(); index++) {
            JsonObject candidate = row(valuations, index);
            if (candidate == null || !satisfied(candidate)) {
                continue;
            }
            JsonArray witness = array(candidate, "existentialWitness");
            if (witness.size() == 0) {
                continue;
            }
            witnessed++;
            StringBuilder vector = new StringBuilder();
            for (JsonElement element : witness) {
                String value = element.isJsonObject()
                        ? optionalString(element.getAsJsonObject(), "value")
                        : "";
                vector.append(value).append('\0');
                if (!isZero(value)) {
                    allZero = false;
                }
            }
            vectors.add(vector.toString());
        }
        if (witnessed == 0) {
            return null;
        }
        if (allZero) {
            return blocker(WITNESS_UNINFORMATIVE, "ALL_ZERO",
                    "every existential witness value is zero and no"
                            + " perturbation of one was rejected, so the"
                            + " witness is tied to no root");
        }
        if (vectors.size() < 2) {
            return null;
        }
        for (String vector : vectors) {
            if (!vector.equals(vectors.get(0))) {
                return null;
            }
        }
        return blocker(WITNESS_UNINFORMATIVE, "INVARIANT_ACROSS_VALUATIONS",
                "the existential witness is identical across all "
                        + vectors.size() + " satisfying valuations and no"
                        + " perturbation of it was rejected, so it does not"
                        + " depend on the target predicate");
    }

    private static int undecidedValuations(JsonArray valuations) {
        int undecided = 0;
        for (int index = 0; index < valuations.size(); index++) {
            JsonObject candidate = row(valuations, index);
            if (candidate == null) {
                continue;
            }
            String status = optionalString(candidate, "status");
            if (!"sat".equals(status) && !"unsat".equals(status)) {
                undecided++;
            }
        }
        return undecided;
    }

    private static boolean isZero(String value) {
        String trimmed = value == null ? "" : value.trim();
        return "0".equals(trimmed) || "(- 0)".equals(trimmed)
                || "#x0".equals(trimmed) || "false".equals(trimmed);
    }

    private static JsonObject row(JsonArray rows, int index) {
        JsonElement element = rows.get(index);
        return element != null && element.isJsonObject()
                ? element.getAsJsonObject() : null;
    }

    private static boolean satisfied(JsonObject valuation) {
        return "sat".equals(optionalString(valuation, "status"));
    }

    /**
     * Whether the solver answered this valuation at all.
     *
     * <p>{@code satisfied} is false for {@code unsat}, for a timeout and for
     * {@link BooleanReachConditionExtractor#FRONTIER_PINNED_UNSAT} alike, so
     * on its own it cannot tell a refutation from a missing answer.  Every
     * reading that treats "not satisfied" as evidence -- fault sensitivity
     * above all, which reads a sat/not-sat pair one root apart as proof that
     * the root decides the target -- has to ask this first, or an unanswered
     * valuation becomes a finding.</p>
     */
    private static boolean decided(JsonObject valuation) {
        String status = optionalString(valuation, "status");
        return "sat".equals(status) || "unsat".equals(status);
    }

    /**
     * Why this run was accepted, read off the decision it was accepted by.
     *
     * <p>This sentence used to be a constant -- "a valuation satisfies the
     * target predicate inside the recorded model and a symbolic root flips
     * it" -- emitted for every accepted candidate whatever the run did. It
     * consulted no valuation, no marker and no mechanism, so it asserted a
     * root flip on HDFS-17960, whose accepted witness flips nothing and
     * reproduces the value the recording had. A reason nothing computes is
     * not evidence about the run it is attached to, so it is derived here
     * from the same rows {@code witnessFindings} publishes: which valuation
     * the acceptance rests on, which roots that valuation moved or left
     * alone, which mechanisms explained it, and whether the root space was
     * shown to decide the target.</p>
     */
    private static String claimReason(String claim, String reachability,
                                      List<JsonObject> blockers,
                                      String refusals, JsonObject legitimacy,
                                      JsonObject faultMarkers,
                                      boolean faultSensitive) {
        if (SAT_CANDIDATE.equals(claim)) {
            return satCandidateReason(legitimacy, faultMarkers,
                    faultSensitive);
        }
        if (UNSAT_CLOSED.equals(claim)) {
            return "no valuation satisfies the target predicate and the"
                    + " selected model is closed";
        }
        StringBuilder reason = new StringBuilder();
        reason.append(blockers.size()).append(" blocker(s) withhold an")
                .append(" accepted claim from a ").append(reachability)
                .append(" solver result: ");
        for (int index = 0; index < blockers.size(); index++) {
            if (index > 0) {
                reason.append(',');
            }
            reason.append(optionalString(blockers.get(index), "code"));
        }
        if (!refusals.isEmpty()) {
            reason.append("; Composer refusals: ").append(refusals);
        }
        return reason.toString();
    }

    /**
     * The accepted witness, named: which valuation, what it moved, what
     * explained it, and what the root space was shown to do.
     */
    private static String satCandidateReason(JsonObject legitimacy,
                                             JsonObject faultMarkers,
                                             boolean faultSensitive) {
        int ordinal = optionalInteger(legitimacy,
                "acceptedValuationOrdinal", -1);
        JsonObject accepted = null;
        for (JsonElement element : array(legitimacy, "valuations")) {
            if (element.isJsonObject() && optionalInteger(
                    element.getAsJsonObject(), "valuationOrdinal", -1)
                    == ordinal) {
                accepted = element.getAsJsonObject();
            }
        }
        if (accepted == null) {
            return "the solver reached the target predicate and no blocker"
                    + " withholds the claim; no enumerated valuation was"
                    + " named as the one the acceptance rests on";
        }
        StringBuilder reason = new StringBuilder();
        reason.append("valuation ").append(ordinal)
                .append(" satisfies the target predicate inside the recorded"
                        + " model");
        JsonArray flipped = array(accepted, "flippedMarkers");
        if (flipped.size() > 0) {
            reason.append(" and moves ").append(flipped.size())
                    .append(" declared root(s) off what they recorded: ")
                    .append(markerSummary(flipped));
        } else if (array(accepted, "markerAssignment").size() > 0) {
            reason.append(" with every declared root at the value the"
                            + " recording had (")
                    .append(markerSummary(array(accepted,
                            "markerAssignment")))
                    .append("), so the witness reproduces the recorded case"
                            + " rather than a counterfactual");
        } else {
            reason.append(" and declares no symbolic root to move");
        }
        String mechanisms = mechanismSummary(array(accepted, "mechanisms"));
        String kind = optionalString(accepted,
                WitnessLegitimacy.FINDING_KIND);
        // The finding kind first, because it is the claim; the mechanism
        // rows behind it are how it was reached. "No named mechanism was
        // needed" was the sentence an empty list used to print, and it read
        // as a property of the run rather than as the absence it was.
        reason.append("; a ").append(firstNonEmpty(kind, "finding of no named"
                + " kind")).append(" finding");
        if (!mechanisms.isEmpty()) {
            reason.append(", explained by ").append(mechanisms);
        }
        reason.append("; ").append(faultSensitive
                ? "the root space decides the target"
                : "no enumerated root flip changes the target predicate");
        String deciding = decidingMarkers(faultMarkers);
        if (!deciding.isEmpty()) {
            reason.append(" (").append(deciding).append(')');
        }
        return reason.toString();
    }

    /** Each marker named with the value this valuation gave it. */
    private static String markerSummary(JsonArray rows) {
        List<String> named = new ArrayList<>();
        for (JsonElement element : rows) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject row = element.getAsJsonObject();
            StringBuilder text = new StringBuilder();
            text.append(firstNonEmpty(optionalString(row, "sourceIdentity"),
                    optionalString(row, "solverTerm")));
            String where = firstNonEmpty(optionalString(row, "siteId"),
                    optionalString(row, "portId"));
            if (!where.isEmpty()) {
                text.append(" (").append(where).append(')');
            }
            text.append(" = ").append(optionalBool(row, "value", false));
            if (!optionalBool(row, "recordedPolarityStated", false)) {
                // Said out loud, and not guessed past: nothing observed this
                // root's recorded value, so there is no polarity to compare
                // the witness against and none is invented here.
                String conflict = optionalString(row,
                        "recordedValueConflict");
                text.append(conflict.isEmpty()
                        ? " [no recorded value observed]"
                        : " [recorded value disputed: " + conflict + "]");
            }
            named.add(text.toString());
        }
        return String.join(", ", named);
    }

    /** Each named mechanism, once, with a count where it repeats. */
    private static String mechanismSummary(JsonArray mechanisms) {
        Map<String, Integer> counts = new LinkedHashMap<>();
        for (JsonElement element : mechanisms) {
            if (!element.isJsonObject()) {
                continue;
            }
            String kind = optionalString(element.getAsJsonObject(), "kind");
            if (kind.isEmpty()) {
                continue;
            }
            Integer held = counts.get(kind);
            counts.put(kind, held == null ? 1 : held + 1);
        }
        List<String> named = new ArrayList<>();
        for (Map.Entry<String, Integer> entry : counts.entrySet()) {
            named.add(entry.getValue() > 1
                    ? entry.getKey() + " x" + entry.getValue()
                    : entry.getKey());
        }
        return String.join(", ", named);
    }

    /** The markers the evidence shows decide the target, and how. */
    private static String decidingMarkers(JsonObject faultMarkers) {
        List<String> named = new ArrayList<>();
        for (JsonElement element : array(faultMarkers, "markers")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject row = element.getAsJsonObject();
            if (!optionalBool(row, "polarityDecides", false)) {
                continue;
            }
            named.add(firstNonEmpty(optionalString(row, "sourceIdentity"),
                    optionalString(row, "portId"))
                    + (optionalBool(row, "reachesAtRecordedValue", false)
                    ? " reaches the target at its recorded value and at no"
                    + " other"
                    : " reaches the target only when moved off what it"
                    + " recorded"));
        }
        return String.join("; ", named);
    }

    /** One line per blocker: the whole reason a run was not accepted. */
    private static String whyNotAccepted(String claim,
                                         List<JsonObject> blockers) {
        if (blockers.isEmpty()) {
            return "";
        }
        StringBuilder summary = new StringBuilder();
        summary.append("claim=").append(claim).append(": ")
                .append(blockers.size())
                .append(" blocker(s) withhold acceptance");
        for (JsonObject row : blockers) {
            String subject = optionalString(row, "subject");
            summary.append(System.lineSeparator()).append("  ")
                    .append(optionalString(row, "code"));
            if (!subject.isEmpty()) {
                summary.append(" [").append(subject).append(']');
            }
            summary.append(": ").append(optionalString(row, "detail"));
        }
        return summary.toString();
    }

    /**
     * One finding per observed target occurrence the composition left out.
     *
     * <p>Silent when the recording observed the annotated site once, which
     * is the ordinary case and the one every existing corpus rests on.</p>
     */
    static List<JsonObject> uncomposedTargetOccurrences(JsonObject manifest) {
        JsonArray occurrences = array(manifest,
                ComposedManifest.TARGET_REACH_OCCURRENCES);
        List<JsonObject> result = new ArrayList<>();
        if (occurrences.size() < 2) return result;
        String composed = "";
        for (JsonElement element : occurrences) {
            if (element.isJsonObject() && optionalBool(
                    element.getAsJsonObject(), "composed", false)) {
                composed = optionalString(element.getAsJsonObject(),
                        "occurrenceId");
            }
        }
        for (JsonElement element : occurrences) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            if (optionalBool(row, "composed", false)) continue;
            result.add(blocker(TARGET_OCCURRENCE_NOT_COMPOSED,
                    optionalString(row, "occurrenceId"),
                    "the recording observed the annotated target at "
                            + occurrences.size() + " occurrences and this"
                            + " composition lowered "
                            + (composed.isEmpty() ? "none of them"
                            : composed)
                            + ": nothing here states whether the target is"
                            + " reachable at "
                            + optionalString(row, "occurrenceId")
                            + " " + row.getAsJsonArray("failureSites")));
        }
        return result;
    }

    private static JsonObject blocker(String code, String subject,
                                      String detail) {
        JsonObject row = new JsonObject();
        row.addProperty("code", code);
        row.addProperty("subject", subject == null ? "" : subject);
        row.addProperty("detail", detail);
        return row;
    }

    /**
     * Adds every blocking gap row of {@code rows} to {@code hardGaps}.
     *
     * <p>The class comes from {@link GapLedger}, which is fail-closed: a code
     * nobody registered is blocking, so a new gap withholds a claim until
     * somebody states why it cannot break a chain.</p>
     */
    private static void collectBlocking(Set<String> hardGaps, String stage,
                                        JsonArray rows) {
        for (JsonElement row : rows) {
            String code = code(row);
            if (code.isEmpty() || !GapLedger.blocking(code)) continue;
            hardGaps.add(stage + "/" + code);
        }
    }

    private static String code(JsonElement element) {
        if (element == null) {
            return "";
        }
        if (element.isJsonObject()) {
            JsonObject row = element.getAsJsonObject();
            return firstNonEmpty(optionalString(row, "code"),
                    firstNonEmpty(optionalString(row, "reason"),
                            optionalString(row, "kind")));
        }
        return element.isJsonPrimitive() ? element.getAsString() : "";
    }

    private static String codes(JsonArray rows) {
        Set<String> unique = new LinkedHashSet<>();
        for (JsonElement element : rows) {
            String code = code(element);
            if (!code.isEmpty()) {
                unique.add(code);
            }
        }
        return String.join(",", unique);
    }

    private static String firstNonEmpty(String value, String fallback) {
        return value == null || value.trim().isEmpty() ? fallback : value;
    }
}
