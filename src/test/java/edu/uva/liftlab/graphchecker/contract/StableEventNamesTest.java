package edu.uva.liftlab.graphchecker.contract;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

import org.junit.Test;

/** A context's name across runs: no counts, each hop its sender's first send. */
public class StableEventNamesTest {
    private static final String TASK = "n0|Root:TASK#4|<A: void call()>@0><H: void submit()>#u9@";

    @Test
    public void aHopIsItsSendersFirstSendOfTheSiteWhateverCameBefore() {
        StableEventNames confirmed = new StableEventNames();
        confirmed.sent(TASK + "1", "HTTP:STATUS", "e1");
        confirmed.sent(TASK + "2", "HTTP:STATUS", "e2");     // a poll's second
        confirmed.sent(TASK + "3", "HTTP:SPLIT", "e3");
        StableEventNames nativeRun = new StableEventNames();
        nativeRun.sent(TASK + "1", "HTTP:STATUS", "f1");     // polled once
        nativeRun.sent(TASK + "2", "HTTP:SPLIT", "f2");
        String split = confirmed.context("n1|Anchor:e3@HTTP/TASK|<B: void x()>@3");
        assertEquals("n1|Anchor:{n0|Root:TASK#4|<A: void call()>><H: void submit()>#u9 >HTTP:SPLIT}@HTTP/TASK|<B: void x()>",
                split);
        assertEquals(split, nativeRun.context("n1|Anchor:f2@HTTP/TASK|<B: void x()>@5"));
        assertNull("a loop's later send has no fixed name",
                confirmed.context("n1|Anchor:e2@HTTP/TASK"));
        assertNull("a send this run never made", nativeRun.context("n1|Anchor:e3@HTTP/TASK"));
        assertEquals("plain|context", confirmed.context("plain|context@7"));
    }
}
