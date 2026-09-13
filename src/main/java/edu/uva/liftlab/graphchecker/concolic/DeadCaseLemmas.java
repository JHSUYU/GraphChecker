package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
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
     * Probes every arm of every multi-arm partition and returns the formula
     * with one named lemma per refuted arm, plus the ledger of every probe.
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
        ledger.addProperty("schemaVersion", 1);
        ledger.addProperty("kind", KIND);
        ledger.addProperty("authority", AUTHORITY);
        ledger.addProperty("solver", solver == null ? "" : solver.toString());
        ledger.addProperty("armRlimit", armRlimit);
        JsonArray probes = new JsonArray();
        JsonArray lemmas = new JsonArray();
        List<List<String>> arms = multiArmPartitions(partitions);
        String skipped = solver == null ? "NO_SOLVER"
                : armRlimit <= 0L ? "DISABLED"
                : smtLib.contains(FAIL_CLOSED_MARKER) ? "FAIL_CLOSED"
                : smtLib.lastIndexOf(CHECK_SAT) < 0 ? "NO_CHECK_SAT"
                : arms.isEmpty() ? "NO_MULTI_ARM_PARTITION" : "";
        ledger.addProperty("skipped", skipped);
        if (!skipped.isEmpty()) {
            ledger.addProperty("probedArms", 0);
            ledger.add("probes", probes);
            ledger.add("lemmas", lemmas);
            return new Result(smtLib, ledger);
        }
        int checkSat = smtLib.lastIndexOf(CHECK_SAT);
        String body = smtLib.substring(0, checkSat);
        String tail = smtLib.substring(checkSat);
        String separator = System.lineSeparator();
        List<String> proven = new ArrayList<>();
        Set<String> probed = new LinkedHashSet<>();
        for (List<String> partition : arms) {
            for (String selector : partition) {
                if (!probed.add(selector)) continue;
                StringBuilder query = new StringBuilder(body.length() + 512);
                query.append("(set-option :rlimit ").append(armRlimit)
                        .append(')').append(separator);
                query.append(body);
                for (String lemma : proven) {
                    query.append(lemmaAssertion(lemma)).append(separator);
                }
                query.append("(assert ").append(selector).append(')')
                        .append(separator).append(CHECK_SAT)
                        .append(separator);
                long started = System.nanoTime();
                ConcolicConstraintSolver.SolverOutput output =
                        ConcolicConstraintSolver.run(solver,
                                query.toString(), ARM_WALL_MILLIS);
                long elapsed = Math.max(0L,
                        (System.nanoTime() - started) / 1_000_000L);
                String status = output.status();
                JsonObject probe = new JsonObject();
                probe.addProperty("selector", selector);
                probe.addProperty("status", status);
                probe.addProperty("elapsedMillis", elapsed);
                probe.addProperty("carriedLemmas", proven.size());
                probes.add(probe);
                if (!"unsat".equals(status)) continue;
                proven.add(selector);
                JsonObject lemma = new JsonObject();
                lemma.addProperty("selector", selector);
                lemma.addProperty("lemma", lemmaName(selector));
                JsonArray siblings = new JsonArray();
                for (String sibling : partition) siblings.add(sibling);
                lemma.add("partition", siblings);
                lemmas.add(lemma);
            }
        }
        ledger.addProperty("probedArms", probed.size());
        ledger.add("probes", probes);
        ledger.add("lemmas", lemmas);
        if (proven.isEmpty()) return new Result(smtLib, ledger);
        StringBuilder rendered = new StringBuilder(smtLib.length()
                + proven.size() * 160);
        rendered.append(body);
        for (String selector : proven) {
            rendered.append(lemmaAssertion(selector)).append(separator);
        }
        rendered.append(tail);
        return new Result(rendered.toString(), ledger);
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
