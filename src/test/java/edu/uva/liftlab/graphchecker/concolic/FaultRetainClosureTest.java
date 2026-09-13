package edu.uva.liftlab.graphchecker.concolic;

import org.junit.Assume;
import org.junit.Test;

import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * A caught transport failure retains the previous state; it does not erase it.
 *
 * <p>The corpus is the smallest shape that can tell retention from erasure.
 * Two writers publish to {@code x}: {@code W1} leaves 1, and {@code W2} --
 * the occurrence a request-fault marker controls -- leaves 2.  A reader
 * {@code R} observes {@code x}.  With the marker false the read must see 2,
 * because last-writer-wins says the later writer is the one it saw; with the
 * marker true {@code W2} never ran, so the read must see 1.  Nothing about
 * the read's own encoding changes between the two: the marker idles the
 * writer's case, the arm that needs that case becomes unselectable, and the
 * previous version is what is left.</p>
 *
 * <p>The second half is the part a formula gets wrong by omission.  A
 * downstream region {@code D} reads {@code y}, which only {@code W2} writes.
 * If {@code D} keeps an unconditional exactly-one partition, the marker true
 * forces {@code D} to run with nothing to read and the formula is
 * contradictory by construction -- which is what made every fault-true
 * valuation of hdfs-17899-bug1 come back unsat.  The closure idles {@code D}
 * on the same marker instead, and reports the location that lost its value.
 * </p>
 */
public class FaultRetainClosureTest {
    private static final String MARKER = "marker";
    private static final String W1_CASE = "case_selector__w1";
    private static final String W2_CASE = "case_selector__w2";
    private static final String R_CASE = "case_selector__r";
    private static final String D_CASE = "case_selector__d";
    private static final String N_CASE = "case_selector__n";
    private static final String INITIAL_CASE = "case_selector__initial";
    private static final String X_FROM_INITIAL = "read_x_from_initial";
    private static final String X_FROM_W1 = "read_x_from_w1";
    private static final String X_FROM_W2 = "read_x_from_w2";
    private static final String Y_FROM_W2 = "read_y_from_w2";
    private static final String Z_FROM_N = "read_z_from_n";

    /** The closure follows the marker past its own consumer. */
    @Test
    public void closureIdlesTheRegionsTheIdledWriterFed() {
        ConcolicSmtComposer.FaultIdleClosure closure =
                ConcolicSmtComposer.faultIdleClosure(
                        Collections.singletonList(W2_CASE),
                        readArms(), readOwners());

        assertEquals(new LinkedHashSet<>(Arrays.asList(W2_CASE, D_CASE)),
                closure.idledCaseSelectors);
        // R keeps W1's arm, so it is not starved and R still runs.
        assertEquals(Collections.singleton("read_y"), closure.starvedReads);
        assertFalse(closure.idledCaseSelectors.contains(R_CASE));
        assertFalse(closure.idledCaseSelectors.contains(W1_CASE));
        // N writes a location this marker has nothing to do with, and its
        // reader is untouched: the marker idles its own consumer and what
        // depends on that consumer, and stops there.
        assertFalse(closure.idledCaseSelectors.contains(N_CASE));
        assertFalse(closure.starvedReads.contains("read_z"));
    }

    /** An idled writer leaves the location's previous version in place. */
    @Test
    public void faultTrueRetainsThePreviousWriterValue() throws Exception {
        Assume.assumeTrue(z3Available());
        String model = retainModel(true);

        // The marker false is the recorded run: the later writer wins.
        assertEquals("unsat", solve(model + assertion("(not " + MARKER + ")")
                + assertion("(not (= x 2))")));
        assertEquals("sat", solve(model + assertion("(not " + MARKER + ")")
                + assertion("(= x 2)")));
        // The marker true idles W2, and the read falls back to W1's value:
        // the predecessor in the guarded-read order, not the location's
        // INITIAL version, which is still a candidate arm and still 0.
        assertEquals("unsat", solve(model + assertion(MARKER)
                + assertion("(not (= x 1))")));
        assertEquals("sat", solve(model + assertion(MARKER)
                + assertion("(= x 1)")));
        assertEquals("unsat", solve(model + assertion(MARKER)
                + assertion("(= x 0)")));
        // The INITIAL version is the fallback, not the retained value: it
        // is reached only where the marker idles every tracked writer, which
        // is the read of y below, not this one.
        assertEquals("unsat", solve(model + assertion(MARKER)
                + assertion(X_FROM_INITIAL)));
        assertEquals("unsat", solve(model + assertion("(not " + MARKER + ")")
                + assertion(X_FROM_INITIAL)));
    }

    /** A region the marker does not reach keeps running and keeps its value. */
    @Test
    public void anUnrelatedWriterIsUntouchedByTheMarker() throws Exception {
        Assume.assumeTrue(z3Available());
        String model = retainModel(true);

        assertEquals("unsat", solve(model + assertion(MARKER)
                + assertion("(not " + N_CASE + ")")));
        assertEquals("unsat", solve(model + assertion(MARKER)
                + assertion("(not (= z 9))")));
        assertEquals("unsat", solve(model + assertion("(not " + MARKER + ")")
                + assertion("(not (= z 9))")));
    }

    /**
     * The downstream region stays satisfiable, and only because of the
     * closure: with its partition left unconditional the same marker makes
     * the formula unsat.
     */
    @Test
    public void faultTrueLeavesTheDownstreamRegionSatisfiable()
            throws Exception {
        Assume.assumeTrue(z3Available());

        assertEquals("sat", solve(retainModel(true) + assertion(MARKER)));
        assertEquals("unsat", solve(retainModel(false) + assertion(MARKER)));
        // Neither encoding changes the recorded run.
        assertEquals("sat", solve(retainModel(true)
                + assertion("(not " + MARKER + ")")));
        assertEquals("sat", solve(retainModel(false)
                + assertion("(not " + MARKER + ")")));
    }

    /** A marker true forbids every case; a marker false partitions them. */
    @Test
    public void faultControlledPartitionIdlesOnlyUnderTheMarker()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String partition = ConcolicSmtComposer.faultControlledPartition(
                MARKER, Arrays.asList("case_b", "case_a"));
        String common = declarations(MARKER, "case_a", "case_b")
                + assertion(partition);

        assertEquals("unsat", solve(common + assertion(MARKER)
                + assertion("case_a")));
        assertEquals("unsat", solve(common + assertion(MARKER)
                + assertion("case_b")));
        assertEquals("sat", solve(common + assertion(MARKER)));
        assertEquals("unsat", solve(common + assertion("(not " + MARKER + ")")
                + assertion("(and case_a case_b)")));
        assertEquals("unsat", solve(common + assertion("(not " + MARKER + ")")
                + assertion("(and (not case_a) (not case_b))")));
        assertEquals("sat", solve(common + assertion("(not " + MARKER + ")")
                + assertion("case_a")));
    }

    /**
     * The contract the reach driver depends on: a selector a marker decides
     * is advertised as conditional and nowhere else.
     */
    @Test
    public void faultControlledSelectorsAreNeverOfferedForPinning() {
        String smt = "(assert (! (and (=> marker (not "
                + W2_CASE + ")) (=> (not marker) (= (+ (ite " + W2_CASE
                + " 1 0)) 1))) :named request_fault_control__CTRL_ONE))\n"
                + "(assert (! (= (+ (ite " + W1_CASE
                + " 1 0)) 1) :named region_case_selector_partition_W1))\n";
        Set<String> controlled =
                ConcolicSmtComposer.faultControlledSelectorsIn(smt);
        assertEquals(Collections.singleton(W2_CASE), controlled);

        List<List<String>> unconditional = Collections.singletonList(
                Collections.singletonList(W1_CASE));
        List<List<String>> conditional = Collections.singletonList(
                Collections.singletonList(W2_CASE));
        assertTrue(ConcolicSmtComposer.unsplitFaultControlledSelectors(
                controlled, unconditional, conditional).isEmpty());

        // The shape the closure-cap build shipped: the controlled selector
        // is advertised for pinning, so the driver can freeze the marker.
        List<List<String>> unsplit = Arrays.asList(
                Collections.singletonList(W1_CASE),
                Collections.singletonList(W2_CASE));
        assertEquals(Collections.singletonList(W2_CASE),
                ConcolicSmtComposer.unsplitFaultControlledSelectors(
                        controlled, unsplit, conditional));
        // And the shape where it is advertised in neither list.
        assertEquals(Collections.singletonList(W2_CASE),
                ConcolicSmtComposer.unsplitFaultControlledSelectors(
                        controlled, unconditional,
                        Collections.<List<String>>emptyList()));
    }

    /**
     * The pairs the manifest carries: what each thinned read falls back to.
     *
     * <p>{@code read_x} keeps {@code W1}'s version, which is the predecessor
     * of the arm the marker idled and not the location's INITIAL arm.
     * {@code read_y} has no surviving arm at all, so its retained arm is
     * empty and the composer reports it as a starved read instead.  {@code
     * read_z} is untouched, so it contributes no row: a read the marker did
     * not thin has nothing to narrate.</p>
     */
    @Test
    public void retainedVersionsNameThePredecessorEachReadFallsBackTo() {
        ConcolicSmtComposer.FaultIdleClosure closure =
                ConcolicSmtComposer.faultIdleClosure(
                        Collections.singletonList(W2_CASE),
                        readArms(), readOwners());
        List<ConcolicSmtComposer.RetainedVersion> retained =
                ConcolicSmtComposer.retainedVersions(readOrders(), readArms(),
                        closure.idledCaseSelectors);

        assertEquals(2, retained.size());
        ConcolicSmtComposer.RetainedVersion x = retained.get(0);
        assertEquals("read_x", x.readIdentity);
        assertEquals("read_x\nuse", x.orderScope);
        assertEquals(Collections.singletonList(X_FROM_W2), x.idledArms);
        assertEquals(X_FROM_W1, x.retainedArm);

        ConcolicSmtComposer.RetainedVersion y = retained.get(1);
        assertEquals("read_y", y.readIdentity);
        assertEquals(Collections.singletonList(Y_FROM_W2), y.idledArms);
        assertEquals("", y.retainedArm);
        assertTrue(closure.starvedReads.contains(y.readIdentity));
    }

    /**
     * Idling every writer of a location falls the read back to INITIAL, and
     * the read is then not starved: a retained prior version is a version.
     */
    @Test
    public void retainedVersionsFallBackToTheInitialArm() {
        Map<String, Map<String, List<String>>> arms = readArms();
        List<ConcolicSmtComposer.RetainedVersion> retained =
                ConcolicSmtComposer.retainedVersions(readOrders(), arms,
                        Arrays.asList(W1_CASE, W2_CASE));

        ConcolicSmtComposer.RetainedVersion x = retained.get(0);
        assertEquals(Arrays.asList(X_FROM_W1, X_FROM_W2), x.idledArms);
        assertEquals(X_FROM_INITIAL, x.retainedArm);
        assertFalse(ConcolicSmtComposer.faultIdleClosure(
                Arrays.asList(W1_CASE, W2_CASE), arms, readOwners())
                .starvedReads.contains("read_x"));
    }

    /** One order chain per read, arms earliest first. */
    private static Map<String, List<String>> readOrders() {
        Map<String, List<String>> orders = new LinkedHashMap<>();
        orders.put("read_x\nuse", Arrays.asList(X_FROM_INITIAL, X_FROM_W1,
                X_FROM_W2));
        orders.put("read_y\nuse", Collections.singletonList(Y_FROM_W2));
        orders.put("read_z\nuse", Collections.singletonList(Z_FROM_N));
        return orders;
    }

    /**
     * The corpus, as SMT.
     *
     * @param closed whether the closure idled {@code D} on the same marker.
     */
    private static String retainModel(boolean closed) {
        StringBuilder model = new StringBuilder(declarations(MARKER, W1_CASE,
                W2_CASE, R_CASE, D_CASE, N_CASE, INITIAL_CASE,
                X_FROM_INITIAL, X_FROM_W1, X_FROM_W2, Y_FROM_W2, Z_FROM_N));
        model.append("(declare-const x Int)\n")
                .append("(declare-const y Int)\n")
                .append("(declare-const z Int)\n");
        // W2's occurrence is the one the request-fault marker controls.
        model.append(assertion(ConcolicSmtComposer.faultControlledPartition(
                MARKER, Collections.singletonList(W2_CASE))));
        // W1 and R always run.
        model.append(assertion(ConcolicSmtComposer.conditionalExactlyOne(
                        "true", Collections.singletonList(W1_CASE))))
                .append(assertion(ConcolicSmtComposer.conditionalExactlyOne(
                        "true", Collections.singletonList(R_CASE))))
                // N writes a different location and no marker controls it.
                .append(assertion(ConcolicSmtComposer.conditionalExactlyOne(
                        "true", Collections.singletonList(N_CASE))));
        // D either follows the marker, or keeps an unconditional partition.
        model.append(assertion(closed
                ? ConcolicSmtComposer.faultControlledPartition(MARKER,
                Collections.singletonList(D_CASE))
                : ConcolicSmtComposer.conditionalExactlyOne("true",
                Collections.singletonList(D_CASE))));
        // The read of x: one arm per writer case, ordered by program order.
        List<String> xArms = Arrays.asList(X_FROM_INITIAL, X_FROM_W1,
                X_FROM_W2);
        List<String> xActivity = Arrays.asList(INITIAL_CASE, W1_CASE,
                W2_CASE);
        model.append(assertion(ConcolicSmtComposer.conditionalExactlyOne(
                R_CASE, xArms)))
                .append(assertion("(=> " + X_FROM_INITIAL + " (and "
                        + INITIAL_CASE + " (= x 0)))"))
                .append(assertion("(=> " + X_FROM_W1 + " (and " + W1_CASE
                        + " (= x 1)))"))
                .append(assertion("(=> " + X_FROM_W2 + " (and " + W2_CASE
                        + " (= x 2)))"));
        for (String axiom : ConcolicSmtComposer.lastWriterWins(xArms,
                xActivity)) {
            if (!axiom.isEmpty()) model.append(assertion(axiom));
        }
        // The read of y, which only the controlled occurrence writes.
        model.append(assertion(ConcolicSmtComposer.conditionalExactlyOne(
                D_CASE, Collections.singletonList(Y_FROM_W2))))
                .append(assertion("(=> " + Y_FROM_W2 + " (and " + W2_CASE
                        + " (= y 5)))"));
        // The read of z, written only by the region no marker controls.
        model.append(assertion(ConcolicSmtComposer.conditionalExactlyOne(
                N_CASE, Collections.singletonList(Z_FROM_N))))
                .append(assertion("(=> " + Z_FROM_N + " (and " + N_CASE
                        + " (= z 9)))"));
        return model.toString();
    }

    private static Map<String, Map<String, List<String>>> readArms() {
        Map<String, Map<String, List<String>>> reads =
                new LinkedHashMap<>();
        Map<String, List<String>> x = new LinkedHashMap<>();
        // The INITIAL arm is owned by no region case, so no marker can idle
        // it: a location with a retained prior version never starves.
        x.put(X_FROM_INITIAL, Collections.singletonList(INITIAL_CASE));
        x.put(X_FROM_W1, Collections.singletonList(W1_CASE));
        x.put(X_FROM_W2, Collections.singletonList(W2_CASE));
        reads.put("read_x", x);
        Map<String, List<String>> y = new LinkedHashMap<>();
        y.put(Y_FROM_W2, Collections.singletonList(W2_CASE));
        reads.put("read_y", y);
        Map<String, List<String>> z = new LinkedHashMap<>();
        z.put(Z_FROM_N, Collections.singletonList(N_CASE));
        reads.put("read_z", z);
        return reads;
    }

    private static Map<String, Set<String>> readOwners() {
        Map<String, Set<String>> owners = new LinkedHashMap<>();
        owners.put("read_x", Collections.singleton(R_CASE));
        owners.put("read_y", Collections.singleton(D_CASE));
        owners.put("read_z", Collections.singleton(N_CASE));
        return owners;
    }

    private static String declarations(String... names) {
        StringBuilder result = new StringBuilder("(set-logic ALL)\n");
        for (String name : names) {
            result.append("(declare-const ").append(name)
                    .append(" Bool)\n");
        }
        return result.toString();
    }

    private static String assertion(String formula) {
        return "(assert " + formula + ")\n";
    }

    private static String solve(String input) throws Exception {
        Process process = new ProcessBuilder("z3", "-in", "-smt2").start();
        try (OutputStream stream = process.getOutputStream()) {
            stream.write((input + "(check-sat)\n")
                    .getBytes(StandardCharsets.UTF_8));
        }
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        try (InputStream stream = process.getInputStream()) {
            byte[] chunk = new byte[256];
            for (int count; (count = stream.read(chunk)) >= 0; ) {
                output.write(chunk, 0, count);
            }
        }
        assertEquals(0, process.waitFor());
        return new String(output.toByteArray(), StandardCharsets.UTF_8)
                .trim();
    }

    private static boolean z3Available() {
        try {
            return new ProcessBuilder("z3", "-version").start().waitFor()
                    == 0;
        } catch (Exception unavailable) {
            return false;
        }
    }
}
