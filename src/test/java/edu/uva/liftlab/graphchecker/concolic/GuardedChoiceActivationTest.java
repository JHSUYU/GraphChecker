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

    private static boolean z3Available() {
        try {
            return new ProcessBuilder("z3", "-version").start().waitFor()
                    == 0;
        } catch (Exception unavailable) {
            return false;
        }
    }
}
