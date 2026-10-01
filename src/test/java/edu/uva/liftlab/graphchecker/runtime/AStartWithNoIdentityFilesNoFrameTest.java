package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * The k of a start is an ordinal of the level that makes it within one root
 * hop; a thread under no root hop would count for its whole life, so its
 * starts file no frame.  The work so started is unnamed: its siblings differ
 * by nothing an address names, so what it enters before a hop names it opens
 * no occurrence.
 */
public class AStartWithNoIdentityFilesNoFrameTest {
    private static final String ACCEPT = "<a.Acceptor: void run()>#u5";
    private static final SourceRef DN =
            new SourceRef("CLUSTER_NODE", "DATANODE", "hdfs-17897/dn0", 0);

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
        Lineage.resetForTests();
    }

    /** Runs {@code work} on a new thread claiming {@code carrier}. */
    private static <T> T claimed(final Object carrier,
                                 final Function<Object, T> work)
            throws InterruptedException {
        final List<T> result = new ArrayList<T>();
        Thread thread = new Thread(new Runnable() {
            @Override
            public void run() {
                Identity.claimStart(carrier);
                result.add(work.apply(carrier));
            }
        });
        thread.start();
        thread.join(5000L);
        return result.get(0);
    }

    @Test
    public void anAcceptorUnderNoRootHopHandsItsWorkNoFrame()
            throws Exception {
        assertTrue(Identity.contextHere().isLost());
        Object first = new Object();
        Object second = new Object();
        Identity.startWork(ACCEPT, first);
        Identity.startWork(ACCEPT, second);
        Function<Object, String> frame = carrier -> Identity.innermostFrame();
        assertEquals("", claimed(first, frame));
        assertEquals("", claimed(second, frame));
    }

    /**
     * A connection's handler before and after its first message (a
     * DataXceiver's SASL handshake, whose callback region runs inside the
     * handshake's): the region it enters first opens none, the one it enters
     * inside it under the message's scope opens its own.  A start made
     * under a scope names its work, whose first entry opens an occurrence.
     */
    @Test
    public void unnamedWorkOpensNoOccurrenceUntilAHopNamesIt()
            throws Exception {
        Object connection = new Object();
        Identity.startWork(ACCEPT, connection);
        String[] unnamed = claimed(connection, carrier -> {
            String before = opened("REGION.handshake");
            long hop = RuntimeTraceContext.beginRequest(DN, "handshake");
            String after = opened("REGION.handle");
            Identity.regionExit();
            RuntimeTraceContext.endRequest(hop);
            Identity.regionExit();
            return new String[]{before, after};
        });
        assertEquals("before a hop", "none", unnamed[0]);
        assertEquals("under the hop, inside it", "Root:CLIENT/handshake#1",
                unnamed[1]);

        long request = RuntimeTraceContext.beginRequest(DN, "accept");
        Object named = new Object();
        Identity.startWork(ACCEPT, named);
        RuntimeTraceContext.endRequest(request);
        assertEquals("Root:CLIENT/accept#1", claimed(named, carrier -> {
            String first = opened("REGION.handshake");
            Identity.regionExit();
            return first;
        }));
    }

    /**
     * One test names a start and its work: the starter's lineage.  A
     * starter under a hop whose context still renders Lost files its frame;
     * on a pool's thread an unnamed task ends at the next claim there once
     * its work is over, so the next task's entry opens an occurrence.
     */
    @Test
    public void aStartIsNamedByTheStartersLineageAndEndsAtTheNextClaim()
            throws Exception {
        long hop = Lineage.push(DN.key(), Role.UNKNOWN, "accept");
        assertTrue(Identity.contextHere().isLost());
        Object filed = new Object();
        Identity.startWork(ACCEPT, filed);
        Lineage.pop(hop);
        assertEquals(ACCEPT, claimed(filed,
                carrier -> Identity.innermostFrame()));

        Object unnamed = new Object();
        Identity.startWork(ACCEPT, unnamed);
        String[] tasks = claimed(unnamed, carrier -> {
            String first = opened("REGION.task");
            Identity.regionExit();
            Identity.claimStart(new Object());
            String next = opened("REGION.task");
            Identity.regionExit();
            return new String[]{first, next};
        });
        assertEquals("none", tasks[0]);
        assertEquals("Lost:UNKNOWN", tasks[1]);
    }

    /** What one region entry opened: its context, or "none". */
    private static String opened(String region) {
        OccurrenceAddress address = Identity.occurrence(DN.key(), region,
                true);
        if (Identity.openedNone()) return "none";
        return address.context().render();
    }
}
