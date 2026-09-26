package edu.uva.liftlab.graphchecker.runtime;

import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * The k of a start is an ordinal of the level that makes it within one root
 * hop; a thread under no root hop would count for its whole life, so its
 * starts file no frame and the work keeps the identity of its own turn.
 */
public class AStartWithNoIdentityFilesNoFrameTest {
    private static final String ACCEPT = "<a.Acceptor: void run()>#u5";

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
    }

    private static String claimedFrame(final Object carrier)
            throws InterruptedException {
        final String[] frame = new String[1];
        Thread work = new Thread(new Runnable() {
            @Override
            public void run() {
                Identity.claimStart(carrier);
                frame[0] = Identity.innermostFrame();
            }
        });
        work.start();
        work.join(5000L);
        return frame[0];
    }

    @Test
    public void anAcceptorUnderNoRootHopHandsItsWorkNoFrame()
            throws Exception {
        assertTrue(Identity.contextHere().isLost());
        Object first = new Object();
        Object second = new Object();
        Identity.startWork(ACCEPT, first);
        Identity.startWork(ACCEPT, second);
        assertEquals("", claimedFrame(first));
        assertEquals("", claimedFrame(second));
    }
}
