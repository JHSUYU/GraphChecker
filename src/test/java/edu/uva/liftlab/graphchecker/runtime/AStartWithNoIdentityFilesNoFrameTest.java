package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
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
     * A daemon whose service loop's one entry no hop named (started under no
     * root, or before the window): what it enters opens none until a hop
     * names its work, and then the region it stands in -- the outermost one
     * with no name, which owns what it entered -- opens an occurrence under
     * the hop, indexed from the hop's scope base, for as long as the hop
     * stands: each turn is one occurrence, whose decisions count from 1 and
     * whose entries fold into it.  The region's exit ends it too.  A start
     * made under a scope names its work, whose first entry opens an
     * occurrence.
     */
    @Test
    public void unnamedWorkOpensNoOccurrenceUntilAHopNamesIt()
            throws Exception {
        Object daemon = new Object();
        Identity.startWork(ACCEPT, daemon);
        List<String> seen = claimed(daemon, carrier -> {
            List<String> said = new ArrayList<String>();
            said.add(opened("REGION.loop"));
            said.add(opened("REGION.step"));
            said.add("ordinal " + Identity.nextBranchOrdinal("loop#u3"));
            for (String turn : new String[]{"turn", "turn"}) {
                long hop = RuntimeTraceContext.beginRequest(DN, turn);
                said.add(Identity.currentOccurrence(DN.key()).render());
                said.add(opened("REGION.inner"));
                said.add("ordinals " + Identity.nextBranchOrdinal("loop#u3")
                        + "," + Identity.nextBranchOrdinal("loop#u3"));
                Identity.regionExit(null);
                RuntimeTraceContext.endRequest(hop);
                said.add(Identity.currentOccurrence(DN.key()).regionId());
            }
            Identity.regionExit(null);
            long hop = RuntimeTraceContext.beginRequest(DN, "last");
            Identity.regionExit(null);
            said.add(Identity.currentOccurrence(DN.key()).regionId());
            RuntimeTraceContext.endRequest(hop);
            return said;
        });
        String turn = DN.key() + "/region/REGION.loop/ctx:Root:CLIENT/turn#";
        assertEquals(Arrays.asList("none", "none", "ordinal 0",
                turn + "1/idx:", "none", "ordinals 1,2", "ROLE.UNKNOWN",
                turn + "2/idx:", "none", "ordinals 1,2", "ROLE.UNKNOWN",
                "ROLE.CLIENT"), seen);

        long request = RuntimeTraceContext.beginRequest(DN, "accept");
        Object named = new Object();
        Identity.startWork(ACCEPT, named);
        RuntimeTraceContext.endRequest(request);
        assertEquals("Root:CLIENT/accept#1", claimed(named, carrier -> {
            String first = opened("REGION.handshake");
            Identity.regionExit(null);
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
            Identity.regionExit(null);
            Identity.claimStart(new Object());
            String next = opened("REGION.task");
            Identity.regionExit(null);
            return new String[]{first, next};
        });
        assertEquals("none", tasks[0]);
        assertEquals("Lost:UNKNOWN", tasks[1]);
    }

    /**
     * A message unnamed work sends files no producer endpoint: its index
     * would count what sibling threads did (round HG2: every IPC handler's
     * response shared one anchor).  Named by a hop, the same send files one.
     */
    @Test
    public void unnamedWorkSendsUnanchored() {
        assertEquals(null, Identity.messageSent(DN.key(), "IPC", "c1",
                "RESPONSE", "IPC#RESPONSE", null));
        assertEquals("", Interactions.sender("IPC", "c1", "RESPONSE"));
        long hop = Lineage.push(DN.key(), Role.UNKNOWN, "accept");
        try {
            assertTrue(Identity.messageSent(DN.key(), "IPC", "c2",
                    "RESPONSE", "IPC#RESPONSE", null) != null);
        } finally {
            Lineage.pop(hop);
            Interactions.resetForTests();
        }
    }

    /** What one region entry opened: its context, or "none". */
    private static String opened(String region) {
        OccurrenceAddress address = Identity.occurrence(DN.key(), region,
                true);
        if (Identity.openedNone()) return "none";
        return address.context().render();
    }
}
