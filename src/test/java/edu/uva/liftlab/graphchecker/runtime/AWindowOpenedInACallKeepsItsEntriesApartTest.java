package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.junit.Before;
import org.junit.Test;

/**
 * Counts restarted at the window's opening start at 1 for a site the level
 * reached before it ({@code Identity.Counters#reopened}): a call the window
 * opens in names its entries as one it opened before, or after, does.  Round
 * SL1, hdfs-adhoc-39: a DataNode's blockReport handler queued two storage
 * reports through {@code runBlockOp}, the first before the window; the second
 * entry restarted at 0, and both reports' work stood at {@code runBlockOp@0},
 * one address for two activations.
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

    private enum Window { BEFORE, DURING, AFTER }

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
        RecordingWindow.reset();
    }

    @Test
    public void eachQueuedReportStandsApartWhereverTheWindowOpened()
            throws Exception {
        List<String> before = null;
        for (Window window : Window.values()) {
            reset();
            List<String> reports = reports(window);
            assertFalse(window + ": two reports, two addresses " + reports,
                    reports.get(0).equals(reports.get(1)));
            if (before == null) {
                before = reports;
            } else {
                assertEquals(window + " names them as BEFORE does", before,
                        reports);
            }
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
