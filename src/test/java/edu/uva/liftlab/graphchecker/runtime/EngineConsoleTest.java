package edu.uva.liftlab.graphchecker.runtime;

import org.junit.Assert;
import org.junit.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

/**
 * A workload that captures {@code System.err} reads none of the engine's
 * lines: sweep a40h2's FSImage-851 test asserted on its captured error
 * output and failed on the schedule's own diagnostics.
 */
public class EngineConsoleTest {
    @Test
    public void aWorkloadCapturingSystemErrReadsNoEngineLine() {
        PrintStream original = System.err;
        ByteArrayOutputStream captured = new ByteArrayOutputStream();
        System.setErr(new PrintStream(captured, true));
        try {
            EngineConsole.println("Causynth schedule: a line of the engine's");
            EngineConsole.trace(new IllegalStateException("the engine's"));
        } finally {
            System.setErr(original);
        }
        Assert.assertEquals("", captured.toString());
    }
}
