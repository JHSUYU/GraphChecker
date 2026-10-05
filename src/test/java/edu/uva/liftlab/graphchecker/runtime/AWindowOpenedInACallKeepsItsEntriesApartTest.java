package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.junit.Before;
import org.junit.Test;

/**
 * Counts restarted at the window's opening start at 1 for a site the level
 * reached before it ({@code Identity.Counters#reopened}): with m entries
 * before the window, in-window entry j is {@code @(j + [m > 0])}, so a call
 * the window opens in (m = 1) names its entries as one it opened before (m =
 * 0) does, and m = 0 starts at 0 even where the level itself was entered
 * before the window.  Round SL1, hdfs-adhoc-39: the NameNode's blockReport
 * handler serving a DataNode's report queued two storage reports through
 * {@code runBlockOp}, the first before the window; the second entry
 * restarted at 0, and both reports' work stood at {@code runBlockOp@0}, one
 * address for two activations.
 */
public class AWindowOpenedInACallKeepsItsEntriesApartTest {
    private static final SourceRef NODE =
            new SourceRef("CLUSTER_NODE", "NAMENODE", "t/nn0", 0L);
    private static final String HANDLER = "<a.Rpc: java.lang.Object "
            + "blockReport(a.Report[])>";
    private static final String RUN_OP = "<a.Blocks: java.lang.Object "
            + "runBlockOp(java.util.concurrent.Callable)>";
    private static final String ENQUEUE = "<a.Queue: void "
            + "enqueue(java.lang.Runnable)>#u3";

    /** Where the window opens: before the handler; inside it, before its
     *  first report (m = 0); during the first report or after it (m = 1). */
    private enum Window { BEFORE, IN_HANDLER, DURING, AFTER }

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
        RecordingWindow.reset();
    }

    @Test
    public void eachQueuedReportStandsApartWhereverTheWindowOpened()
            throws Exception {
        List<String> expected = new ArrayList<String>();
        for (int report = 0; report < 2; report++) {
            expected.add(HANDLER + "@0/" + RUN_OP + "@" + report + "/"
                    + ENQUEUE + "@0");
        }
        for (Window window : Window.values()) {
            reset();
            assertEquals(window + ": the first report at 0, the second at 1",
                    expected, reports(window));
        }
    }

    /** One handler call queueing two reports, the window opened where
     *  {@code window} says; each report's address where it runs. */
    private static List<String> reports(Window window) throws Exception {
        Object node = new Object();
        RuntimeTraceContext.registerSource(node, NODE);
        if (window == Window.BEFORE) RecordingWindow.open();
        long request = RuntimeTraceContext.beginRequest(node, "report");
        long handler = Identity.enterFrame(HANDLER, null);
        if (window == Window.IN_HANDLER) RecordingWindow.open();
        Object[] items = {new Object(), new Object()};
        for (int report = 0; report < items.length; report++) {
            long op = Identity.enterFrame(RUN_OP, null);
            Identity.startWork(ENQUEUE, items[report]);
            if (report == 0 && window == Window.DURING) RecordingWindow.open();
            Identity.exitFrame(op);
            if (report == 0 && window == Window.AFTER) RecordingWindow.open();
        }
        Identity.exitFrame(handler);
        RuntimeTraceContext.endRequest(request);
        String[] ran = new String[items.length];
        Thread processor = new Thread(() -> {
            for (int report = 0; report < items.length; report++) {
                long claim = Identity.claimStart(items[report]);
                ran[report] = Identity.atScope().render();
                Identity.endClaim(claim);
            }
        });
        processor.start();
        processor.join(5000L);
        return new ArrayList<String>(Arrays.asList(ran));
    }
}
