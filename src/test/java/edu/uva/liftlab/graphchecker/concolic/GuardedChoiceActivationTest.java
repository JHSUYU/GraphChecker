package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;
import org.junit.Assume;
import org.junit.Test;

import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertNull;

/** Focused checks for activation-scoped symbolic choices. */
public class GuardedChoiceActivationTest {

    @Test
    public void sharedArmSemanticsApplyToEveryActiveUse() throws Exception {
        Assume.assumeTrue(z3Available());
        String common = declarations("active_a", "active_b", "selected",
                "writer") + "(declare-const value Int)\n"
                + assertion(ConcolicSmtComposer.conditionalExactlyOne(
                "active_a", Collections.singletonList("selected")))
                + assertion(ConcolicSmtComposer.conditionalExactlyOne(
                "active_b", Collections.singletonList("selected")))
                + assertion("(=> selected (and writer (= value 7)))")
                + assertion("active_a") + assertion("active_b");

        assertEquals("unsat", solve(common + assertion("(not writer)")));
        assertEquals("unsat", solve(common
                + assertion("(not (= value 7))")));
    }

    /**
     * A read with an INITIAL arm and two writers may not observe a writer's
     * value while no writer is active.  Before last-writer-wins the per-arm
     * writer obligation said only "the selected arm's writer ran", so the
     * INITIAL arm could be selected with both writers live and a read could
     * take a value its own program order had already overwritten.
     */
    @Test
    public void lastWriterWinsRejectsAnUnwrittenWriterValue() throws Exception {
        Assume.assumeTrue(z3Available());
        List<String> selectors = Arrays.asList("initial_arm", "writer_one_arm",
                "writer_two_arm");
        List<String> activity = Arrays.asList("initial_case", "writer_one",
                "writer_two");
        List<String> axioms = ConcolicSmtComposer.lastWriterWins(selectors,
                activity);
        assertEquals("", axioms.get(2));

        StringBuilder model = new StringBuilder(declarations("initial_arm",
                "writer_one_arm", "writer_two_arm", "initial_case",
                "writer_one", "writer_two"));
        model.append("(declare-const value Int)\n")
                .append(assertion(ConcolicSmtComposer.conditionalExactlyOne(
                        "true", selectors)))
                // The VM's arm values: the location started at 0 and the two
                // writers left 1 and 2 behind.
                .append(assertion("(=> initial_arm (= value 0))"))
                .append(assertion("(=> writer_one_arm (and writer_one"
                        + " (= value 1)))"))
                .append(assertion("(=> writer_two_arm (and writer_two"
                        + " (= value 2)))"))
                .append(assertion("(=> initial_arm initial_case)"));
        for (String axiom : axioms) {
            if (!axiom.isEmpty()) model.append(assertion(axiom));
        }

        // Observing writer one's value with neither writer active.
        assertEquals("unsat", solve(model + assertion("(= value 1)")
                + assertion("(not writer_one)")
                + assertion("(not writer_two)")));
        // Observing the INITIAL value while a later writer ran anyway.
        assertEquals("unsat", solve(model + assertion("(= value 0)")
                + assertion("writer_two")));
        // Writer one's value is still reachable while writer two stayed out.
        assertEquals("sat", solve(model + assertion("(= value 1)")
                + assertion("writer_one")
                + assertion("(not writer_two)")));
    }

    /**
     * Writers of one shared read may sit in different planned occurrences,
     * and last-writer-wins still decides between them.
     *
     * <p>HDFS-17960 is exactly this shape: {@code snapshotDeletionOrdered}
     * and the snapshot list are written in one occurrence of
     * {@code SnapshotManager.isSnapshotDeletionOrdered} and read in another,
     * and in {@code getNumSnapshots} - the target's own read.  The arm keys
     * are already per writer CASE, and a case belongs to one occurrence, so
     * nothing about the ordering had to change for arms to span occurrences;
     * this pins that.</p>
     */
    @Test
    public void lastWriterWinsSpansWriterOccurrences() throws Exception {
        Assume.assumeTrue(z3Available());
        // Two writers in different planned occurrences, observed in order.
        List<String> selectors = Arrays.asList("initial_arm",
                "occurrence_one_arm", "occurrence_two_arm");
        List<String> activity = Arrays.asList("initial_case",
                "occurrence_one_case", "occurrence_two_case");
        List<String> axioms = ConcolicSmtComposer.lastWriterWins(selectors,
                activity);

        StringBuilder model = new StringBuilder(declarations("initial_arm",
                "occurrence_one_arm", "occurrence_two_arm", "initial_case",
                "occurrence_one_case", "occurrence_two_case"));
        model.append("(declare-const value Int)\n")
                .append(assertion(ConcolicSmtComposer.conditionalExactlyOne(
                        "true", selectors)))
                .append(assertion("(=> initial_arm (= value 0))"))
                .append(assertion("(=> occurrence_one_arm"
                        + " (and occurrence_one_case (= value 1)))"))
                .append(assertion("(=> occurrence_two_arm"
                        + " (and occurrence_two_case (= value 2)))"))
                .append(assertion("(=> initial_arm initial_case)"));
        for (String axiom : axioms) {
            if (!axiom.isEmpty()) model.append(assertion(axiom));
        }

        // Both occurrences wrote, so the reader observes the later one.
        assertEquals("unsat", solve(model + assertion("(= value 1)")
                + assertion("occurrence_one_case")
                + assertion("occurrence_two_case")));
        assertEquals("sat", solve(model + assertion("(= value 2)")
                + assertion("occurrence_one_case")
                + assertion("occurrence_two_case")));
        // Flipping the later occurrence's case condition falls back to the
        // earlier occurrence's value rather than to the initial one.
        assertEquals("sat", solve(model + assertion("(= value 1)")
                + assertion("occurrence_one_case")
                + assertion("(not occurrence_two_case)")));
        assertEquals("unsat", solve(model + assertion("(= value 0)")
                + assertion("occurrence_one_case")
                + assertion("(not occurrence_two_case)")));
        // With neither occurrence's case holding, the read is the initial.
        assertEquals("sat", solve(model + assertion("(= value 0)")
                + assertion("(not occurrence_one_case)")
                + assertion("(not occurrence_two_case)")));
    }

    /**
     * A container read's arms must differ where the mutations between their
     * versions differ.  A writer arm that lowers to the untouched INITIAL
     * state's own expression has lost its PUT/REMOVE chain, and the container
     * is then constrained by nothing but its size domain.
     */
    @Test
    public void aCollapsedContainerArmIsNamed() {
        // The real shape: each version lowers its own mutation walk.
        assertEquals(-1, ConcolicSmtComposer.collapsedContainerArm(
                Arrays.asList("(assoc_has s k)", "(or (= k k1) base)",
                        "(or (= k k2) (or (= k k1) base))"),
                Arrays.asList(true, false, false)));
        // One arm for a read nothing had written yet is not a collapse.
        assertEquals(-1, ConcolicSmtComposer.collapsedContainerArm(
                Collections.singletonList("(assoc_has s k)"),
                Collections.singletonList(true)));
        // Every arm reducing to one expression: the choice decides nothing.
        assertEquals(0, ConcolicSmtComposer.collapsedContainerArm(
                Arrays.asList("(assoc_has s k)", "(assoc_has s k)",
                        "(assoc_has s k)"),
                Arrays.asList(true, false, false)));
        // A writer arm that reads the untouched initial state.
        assertEquals(2, ConcolicSmtComposer.collapsedContainerArm(
                Arrays.asList("(assoc_has s k)", "(or (= k k1) base)",
                        "(assoc_has s k)"),
                Arrays.asList(true, false, false)));
    }

    @Test
    public void guardedReadSortUsesAnchorAndRejectsMixedArms() {
        JsonObject anchored = new JsonObject();
        anchored.addProperty("_java_type", "L");
        anchored.addProperty("replayReadDescriptor", "Ljava/lang/String;");
        assertEquals(VmTermLowering.Sort.STRING,
                ConcolicSmtComposer.guardedReadSort(anchored,
                        VmTermLowering.Sort.REF,
                        Collections.singletonList(
                                VmTermLowering.Sort.STRING)));

        JsonObject erased = new JsonObject();
        erased.addProperty("_java_type", "REF");
        assertNull(ConcolicSmtComposer.guardedReadSort(erased,
                VmTermLowering.Sort.REF,
                Arrays.asList(VmTermLowering.Sort.REF,
                        VmTermLowering.Sort.STRING)));
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

    /**
     * One read event's order is decided by that event's own candidates.
     *
     * <p>A read identity can cover several events, and their candidate lists
     * need not order each other: event A's arms and event B's arms are never
     * both live at one read. Merging them demanded a total order over the
     * union, found none, and abandoned last-writer-wins for the whole read -
     * which let the INITIAL arm be selected while its writer ran, so a read
     * could return the value the location held before the write it is
     * supposed to have seen. Restricting each recorded chain to the arms one
     * use observes gives each event the order it does have.</p>
     */
    @Test
    public void eachUseKeepsTheOrderItsOwnCandidatesWitness() {
        List<List<String>> chains = Arrays.asList(
                Arrays.asList("initialA", "writerA"),
                Arrays.asList("initialB", "writerB"));

        List<List<String>> useA = ConcolicSmtComposer.scopedChains(chains,
                Arrays.asList("initialA", "writerA"));
        assertEquals(1, useA.size());
        assertEquals(Arrays.asList("initialA", "writerA"), useA.get(0));

        List<List<String>> useB = ConcolicSmtComposer.scopedChains(chains,
                Arrays.asList("initialB", "writerB"));
        assertEquals(Arrays.asList("initialB", "writerB"), useB.get(0));

        // The order the use does witness is kept, and the arms of the other
        // event contribute nothing rather than an unordered pair.
        List<String> axioms = ConcolicSmtComposer.lastWriterWins(
                useA.get(0), Arrays.asList("actInitialA", "actWriterA"));
        assertEquals("(=> initialA (and actInitialA (not actWriterA)))",
                axioms.get(0));
        assertEquals("", axioms.get(1));
    }

    /** An arm no chain of this use mentions leaves the use unordered. */
    @Test
    public void aUseWithNoWitnessedChainIsNotOrdered() {
        List<List<String>> chains = Collections.singletonList(
                Arrays.asList("initialB", "writerB"));
        assertTrue(ConcolicSmtComposer.scopedChains(chains,
                Arrays.asList("initialA", "writerA")).isEmpty());
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
