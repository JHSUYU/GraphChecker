package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sha256;

/**
 * Case arms the composed formula itself refutes, asserted as lemmas.
 *
 * <p>An EXPLORE replay can observe a case whose path condition no model of
 * the final composition admits: the arm contradicts the target-reach
 * obligation the formula was composed under.  The formula already says so,
 * but only after the solver has reasoned through the arm's whole cone.  On
 * HDFS-17960 the two dead arms belong to the root's own region -- the
 * ordered-deletion cases of {@code deleteSnapshot} #1 and #2 that an EXPLORE
 * group observed -- and their cones carry the binary searches over free
 * {@code children} lists and the lambda-valued snapshot chains.  z3 spends
 * its entire budget inside those cones before it ever commits to the live
 * sibling: the plain buggy polarity timed out at 600 s, while each arm on
 * its own is decided in 0.3 s and the formula with the dead arm refuted is
 * sat in 0.3 s.</p>
 *
 * <p>Each arm of every unconditional exactly-one partition is therefore
 * asked alone, {@code formula ∧ arm}, under a deterministic resource
 * budget.  An {@code unsat} answer is a theorem of the formula, so
 * {@code (not arm)} is asserted as a named lemma: the model set is
 * unchanged and nothing recorded is assumed, which is what separates this
 * from pinning a case frontier.  A sat, unknown or timed-out answer leaves
 * the arm alone.  Lemmas found earlier are carried into later probes,
 * which is still sound -- a lemma is implied by the formula -- and is what
 * makes the remaining probes cheap once the culprit is found.</p>
 *
 * <p><b>The formula is asked first.</b>  Every arm of an unsatisfiable
 * formula answers {@code unsat}, so on such a formula the pass would
 * "refute" all of them -- including both arms of one exactly-one partition,
 * which is not a statement about any arm but about the composition.  That is
 * what happened to HDFS-17899 bug3 under the replay-group identity axiom: 8
 * probes, 8 lemmas, and a core naming lemmas rather than the contradiction
 * that produced them.  The pass therefore asks {@code formula} alone under
 * the same budget before any arm, and on {@code unsat} emits no lemma and
 * publishes {@value #FORMULA_UNSAT_ROW} instead.  This pass cannot tell
 * "this arm is dead" from "this formula is dead", so where it cannot tell it
 * says so.</p>
 *
 * <p>A second check catches the same shape from the other side, after
 * probing: lemmas that would refute <em>every</em> arm of one partition are
 * dropped rather than asserted.  Such a set says either that the formula is
 * unsatisfiable after all (the probe above answered {@code unknown}) or that
 * this partition's arms are not the ones the formula's own exactly-one
 * constraint ranges over; under neither reading is a lemma a fact about an
 * arm.  Dropping them only weakens what is emitted: the ones that remain
 * were each proven against the formula, and a lemma carried into a later
 * probe stays a theorem whether or not it is asserted in the end.</p>
 *
 * <p>Conditional partitions are never probed: their arms are decided by a
 * fault marker, and refuting one under the marker's recorded value would
 * freeze the marker the way the extractor's frontier once did.  A
 * fail-closed formula is not probed either: every arm of it is trivially
 * dead and a lemma would misreport the composition gap as a refutation.</p>
 */
final class DeadCaseLemmas {
    static final String MANIFEST_FIELD = "deadCaseLemmas";
    static final String LEMMA_PREFIX = "dead_case_lemma__";
    static final String KIND = "DEAD_CASE_LEMMAS";
    static final String AUTHORITY = "COMPOSED_FORMULA_ARM_REFUTATION_V1";
    /** The composed body refutes itself, so no arm of it says anything. */
    static final String SKIPPED_FORMULA_UNSAT = "FORMULA_UNSAT";
    /** Published row: the pass emitted nothing because the body is unsat. */
    static final String FORMULA_UNSAT_ROW =
            "DEAD_CASE_LEMMAS_SKIPPED_FORMULA_UNSAT";
    /** Published row: lemmas that would have emptied one partition. */
    static final String PARTITION_FULLY_REFUTED_ROW =
            "DEAD_CASE_LEMMAS_PARTITION_FULLY_REFUTED";
    /** z3 resource units per arm; deterministic for one solver build. */
    static final long DEFAULT_ARM_RLIMIT = 5_000_000L;
    /** Wall-clock cap per arm, a safety net behind the resource limit. */
    static final long ARM_WALL_MILLIS = 30_000L;
    static final String FAIL_CLOSED_MARKER = "(assert false) ; fail closed";
    private static final String CHECK_SAT = "(check-sat)";

    private DeadCaseLemmas() {
    }

    static final class Result {
        final String smtLib;
        final JsonObject ledger;

        private Result(String smtLib, JsonObject ledger) {
            this.smtLib = smtLib;
            this.ledger = ledger;
        }
    }

    /**
     * Probes the formula, then every arm of every multi-arm partition, and
     * returns the formula with one named lemma per refuted arm plus the
     * ledger of every probe.
     *
     * @param solver   the z3 executable, or {@code null} to leave the
     *                 formula untouched and say so in the ledger
     * @param armRlimit z3 resource units granted to each probe; {@code 0}
     *                 disables the pass
     */
    static Result prove(String smtLib,
                        List<? extends Collection<String>> partitions,
                        Path solver, long armRlimit)
            throws IOException, InterruptedException {
        JsonObject ledger = new JsonObject();
        ledger.addProperty("schemaVersion", 2);
        ledger.addProperty("kind", KIND);
        ledger.addProperty("authority", AUTHORITY);
        ledger.addProperty("solver", solver == null ? "" : solver.toString());
        ledger.addProperty("armRlimit", armRlimit);
        JsonArray probes = new JsonArray();
        JsonArray lemmas = new JsonArray();
        JsonArray rows = new JsonArray();
        List<List<String>> arms = multiArmPartitions(partitions);
        String skipped = solver == null ? "NO_SOLVER"
                : armRlimit <= 0L ? "DISABLED"
                : smtLib.contains(FAIL_CLOSED_MARKER) ? "FAIL_CLOSED"
                : smtLib.lastIndexOf(CHECK_SAT) < 0 ? "NO_CHECK_SAT"
                : arms.isEmpty() ? "NO_MULTI_ARM_PARTITION" : "";
        ledger.addProperty("skipped", skipped);
        if (!skipped.isEmpty()) {
            return finish(ledger, probes, lemmas, rows, 0, smtLib);
        }
        int checkSat = smtLib.lastIndexOf(CHECK_SAT);
        String body = smtLib.substring(0, checkSat);
        String tail = smtLib.substring(checkSat);
        String separator = System.lineSeparator();

        // The formula alone, under the budget an arm gets.  An arm probe
        // answers unsat on an unsatisfiable formula whatever the arm says,
        // so without this answer every "refutation" below is unreadable.
        JsonObject formulaProbe = ask(solver, armRlimit, body,
                Collections.<String>emptyList(), null, separator);
        ledger.add("formulaProbe", formulaProbe);
        if ("unsat".equals(formulaProbe.get("status").getAsString())) {
            ledger.addProperty("skipped", SKIPPED_FORMULA_UNSAT);
            rows.add(row(FORMULA_UNSAT_ROW, AUTHORITY,
                    "the composed formula is unsatisfiable before any case"
                            + " arm is asserted, so every arm probe would"
                            + " answer unsat and no lemma would be a fact"
                            + " about an arm: " + arms.size()
                            + " multi-arm partition(s) left unprobed"));
            return finish(ledger, probes, lemmas, rows, 0, smtLib);
        }

        List<String> proven = new ArrayList<>();
        Set<String> provenSelectors = new LinkedHashSet<>();
        Map<String, JsonObject> lemmaRows = new LinkedHashMap<>();
        Set<String> probed = new LinkedHashSet<>();
        for (List<String> partition : arms) {
            for (String selector : partition) {
                if (!probed.add(selector)) continue;
                JsonObject probe = ask(solver, armRlimit, body, proven,
                        selector, separator);
                probes.add(probe);
                if (!"unsat".equals(probe.get("status").getAsString())) {
                    continue;
                }
                proven.add(selector);
                provenSelectors.add(selector);
                JsonObject lemma = new JsonObject();
                lemma.addProperty("selector", selector);
                lemma.addProperty("lemma", lemmaName(selector));
                JsonArray siblings = new JsonArray();
                for (String sibling : partition) siblings.add(sibling);
                lemma.add("partition", siblings);
                lemmaRows.put(selector, lemma);
            }
        }

        // Refuting every arm of one exactly-one partition is not a finding
        // about an arm, whichever way it happened.  Drop those lemmas.
        Set<String> dropped = new LinkedHashSet<>();
        for (List<String> partition : arms) {
            if (!provenSelectors.containsAll(partition)) continue;
            dropped.addAll(partition);
            rows.add(row(PARTITION_FULLY_REFUTED_ROW,
                    String.join(",", partition),
                    "every arm of one exactly-one partition was refuted, so"
                            + " the lemmas would leave it no arm to select:"
                            + " either the formula is unsatisfiable and the"
                            + " formula probe could not say so, or these"
                            + " arms are not the ones its partition ranges"
                            + " over.  " + partition.size()
                            + " lemma(s) dropped"));
        }
        proven.removeAll(dropped);
        for (String selector : proven) lemmas.add(lemmaRows.get(selector));
        ledger.addProperty("droppedLemmas", dropped.size());

        if (proven.isEmpty()) {
            return finish(ledger, probes, lemmas, rows, probed.size(),
                    smtLib);
        }
        StringBuilder rendered = new StringBuilder(smtLib.length()
                + proven.size() * 160);
        rendered.append(body);
        for (String selector : proven) {
            rendered.append(lemmaAssertion(selector)).append(separator);
        }
        rendered.append(tail);
        return finish(ledger, probes, lemmas, rows, probed.size(),
                rendered.toString());
    }

    /** One probe: the body, the lemmas carried so far and one optional arm. */
    private static JsonObject ask(Path solver, long armRlimit, String body,
                                  List<String> carried, String selector,
                                  String separator)
            throws IOException, InterruptedException {
        StringBuilder query = new StringBuilder(body.length() + 512);
        query.append("(set-option :rlimit ").append(armRlimit)
                .append(')').append(separator);
        query.append(body);
        for (String lemma : carried) {
            query.append(lemmaAssertion(lemma)).append(separator);
        }
        if (selector != null) {
            query.append("(assert ").append(selector).append(')')
                    .append(separator);
        }
        query.append(CHECK_SAT).append(separator);
        long started = System.nanoTime();
        ConcolicConstraintSolver.SolverOutput output =
                ConcolicConstraintSolver.run(solver, query.toString(),
                        ARM_WALL_MILLIS);
        long elapsed = Math.max(0L,
                (System.nanoTime() - started) / 1_000_000L);
        JsonObject probe = new JsonObject();
        if (selector != null) probe.addProperty("selector", selector);
        probe.addProperty("status", output.status());
        probe.addProperty("elapsedMillis", elapsed);
        probe.addProperty("carriedLemmas", carried.size());
        return probe;
    }

    private static JsonObject row(String kind, String subject,
                                  String detail) {
        JsonObject row = new JsonObject();
        row.addProperty("kind", kind);
        row.addProperty("subject", subject);
        row.addProperty("detail", detail);
        return row;
    }

    private static Result finish(JsonObject ledger, JsonArray probes,
                                 JsonArray lemmas, JsonArray rows,
                                 int probedArms, String smtLib) {
        ledger.addProperty("probedArms", probedArms);
        ledger.add("probes", probes);
        ledger.add("lemmas", lemmas);
        ledger.add("rows", rows);
        return new Result(smtLib, ledger);
    }

    static String lemmaName(String selector) {
        return LEMMA_PREFIX + sha256(selector).substring(0, 16);
    }

    static String lemmaAssertion(String selector) {
        return "(assert (! (not " + selector + ") :named "
                + lemmaName(selector) + "))";
    }

    /** Sorted arms of every partition with a choice to make, in order. */
    private static List<List<String>> multiArmPartitions(
            List<? extends Collection<String>> partitions) {
        List<List<String>> result = new ArrayList<>();
        if (partitions == null) return result;
        for (Collection<String> partition : partitions) {
            if (partition == null) continue;
            Set<String> distinct = new TreeSet<>();
            for (String selector : partition) {
                if (selector != null && !selector.isEmpty()) {
                    distinct.add(selector);
                }
            }
            if (distinct.size() > 1) result.add(new ArrayList<>(distinct));
        }
        return result;
    }
}
