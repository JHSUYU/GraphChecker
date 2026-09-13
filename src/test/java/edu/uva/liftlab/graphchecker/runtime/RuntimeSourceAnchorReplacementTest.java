package edu.uva.liftlab.graphchecker.runtime;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * An application may replace the anchor object it registered with a
 * value-equal successor.  HDFS does exactly that: {@code DataNode.id} is
 * reassigned to a fresh {@code DatanodeRegistration} on every DataNode
 * re-registration, so a workload that registered {@code getDatanodeId()}
 * before a block-report lease expired passes a different object afterwards.
 */
public class RuntimeSourceAnchorReplacementTest {
    private static final SourceRef DN0 =
            new SourceRef("CLUSTER_NODE", "DATANODE", "hdfs-11741/dn0", 0L);
    private static final SourceRef DN1 =
            new SourceRef("CLUSTER_NODE", "DATANODE", "hdfs-11741/dn1", 0L);

    @Before
    public void clearRegistry() {
        RuntimeTraceContext.resetForTests();
    }

    @After
    public void clearRegistryAfter() {
        RuntimeTraceContext.resetForTests();
    }

    @Test
    public void aReplacedAnchorStillNamesTheSourceItRegistered() {
        NodeAnchor registered = new NodeAnchor("127.0.0.1:50010", "uuid-0");
        RuntimeTraceContext.registerSource(registered, DN0);

        NodeAnchor reregistered = new NodeAnchor("127.0.0.1:50010", "uuid-0");
        long request = RuntimeTraceContext.beginRequest(
                reregistered, "refresh-block-keys");
        assertEquals("hdfs-11741/dn0#epoch0/request/refresh-block-keys#1",
                RuntimeTraceContext.current().requestKey);
        assertEquals(DN0, RuntimeTraceContext.current().source);
        RuntimeTraceContext.endRequest(request);

        // The successor is the identity every later lookup carries, so the
        // rebind happens once rather than on each request.
        assertSame(DN0, RuntimeTraceContext.sourceFor(reregistered));
    }

    @Test
    public void anAliasAndARestartAcceptTheSameReplacedAnchor() {
        NodeAnchor registered = new NodeAnchor("127.0.0.1:50010", "uuid-0");
        RuntimeTraceContext.registerSource(registered, DN0);

        NodeAnchor reregistered = new NodeAnchor("127.0.0.1:50010", "uuid-0");
        Object secretManager = new Object();
        assertSame(DN0, RuntimeTraceContext.registerSourceAlias(
                secretManager, reregistered));

        SourceRef restarted = new SourceRef(
                "CLUSTER_NODE", "DATANODE", "hdfs-11741/dn0", 1L);
        assertEquals(restarted, RuntimeTraceContext.restartSource(
                new NodeAnchor("127.0.0.1:50010", "uuid-0"), restarted));
    }

    @Test
    public void twoRegisteredAnchorsAnsweringToItResolveNothing() {
        // Equality that ignores the identity the sources were split on: the
        // successor cannot say which of the two logical nodes it is.
        AddressOnlyAnchor dn0 = new AddressOnlyAnchor("127.0.0.1:50010");
        AddressOnlyAnchor dn1 = new AddressOnlyAnchor("127.0.0.1:50010");
        RuntimeTraceContext.registerSource(dn0, DN0);
        RuntimeTraceContext.registerSource(dn1, DN1);

        AddressOnlyAnchor successor = new AddressOnlyAnchor("127.0.0.1:50010");
        try {
            RuntimeTraceContext.beginRequest(successor, "refresh-block-keys");
            fail("an ambiguous anchor must not be resolved to either source");
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(),
                    refused.getMessage().startsWith(
                            "request source alias is not registered"));
        }
        assertNull(RuntimeTraceContext.sourceFor(successor));
    }

    @Test
    public void anIdentityOnlyAnchorIsStillRefusedAndIsNamed() {
        Object registered = new Object();
        RuntimeTraceContext.registerSource(registered, DN0);
        try {
            RuntimeTraceContext.beginRequest(new Object(), "balance-block");
            fail("an object with no value equality names no source");
        } catch (IllegalArgumentException refused) {
            String message = refused.getMessage();
            assertTrue(message, message.startsWith(
                    "request source alias is not registered"));
            // The refusal has to say which anchor and which request, or the
            // campaign that dies four stages later cannot be traced back.
            assertTrue(message, message.contains("java.lang.Object@"));
            assertTrue(message, message.contains("balance-block"));
        }
    }

    @Test
    public void anUnrelatedValueEqualObjectDoesNotBorrowASource() {
        RuntimeTraceContext.registerSource(
                new NodeAnchor("127.0.0.1:50010", "uuid-0"), DN0);
        try {
            RuntimeTraceContext.beginRequest(
                    new NodeAnchor("127.0.0.1:50020", "uuid-1"), "heartbeat");
            fail("a different node must not inherit dn0's source");
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(),
                    refused.getMessage().startsWith(
                            "request source alias is not registered"));
        }
    }

    /** A DatanodeID-shaped anchor: equal by transfer address and uuid. */
    private static final class NodeAnchor {
        private final String address;
        private final String uuid;

        NodeAnchor(String address, String uuid) {
            this.address = address;
            this.uuid = uuid;
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) return true;
            if (!(other instanceof NodeAnchor)) return false;
            NodeAnchor value = (NodeAnchor) other;
            return address.equals(value.address) && uuid.equals(value.uuid);
        }

        @Override
        public int hashCode() {
            return address.hashCode() * 31 + uuid.hashCode();
        }
    }

    /** Value equality too coarse to separate the sources registered on it. */
    private static final class AddressOnlyAnchor {
        private final String address;

        AddressOnlyAnchor(String address) {
            this.address = address;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof AddressOnlyAnchor
                    && address.equals(((AddressOnlyAnchor) other).address);
        }

        @Override
        public int hashCode() {
            return address.hashCode();
        }
    }
}
