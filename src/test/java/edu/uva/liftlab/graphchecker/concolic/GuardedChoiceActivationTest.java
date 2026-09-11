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

    @Test
    public void guardedReadSortUsesAnchorAndRejectsMixedArms() {
        JsonObject anchored = new JsonObject();
        anchored.addProperty("_java_type", "L");
        anchored.addProperty("replayReadDescriptor", "Ljava/lang/String;");
        assertEquals(ConcolicSmtComposer.Sort.STRING,
                ConcolicSmtComposer.guardedReadSort(anchored,
                        ConcolicSmtComposer.Sort.REF,
                        Collections.singletonList(
                                ConcolicSmtComposer.Sort.STRING)));

        JsonObject erased = new JsonObject();
        erased.addProperty("_java_type", "REF");
        assertNull(ConcolicSmtComposer.guardedReadSort(erased,
                ConcolicSmtComposer.Sort.REF,
                Arrays.asList(ConcolicSmtComposer.Sort.REF,
                        ConcolicSmtComposer.Sort.STRING)));
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
