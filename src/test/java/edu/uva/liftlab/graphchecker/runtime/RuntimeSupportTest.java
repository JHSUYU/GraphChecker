package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileFilter;
import java.io.FilenameFilter;
import java.io.PrintStream;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadInfo;
import java.lang.management.ThreadMXBean;
import java.lang.ref.WeakReference;
import java.math.BigInteger;
import java.nio.file.Files;
import java.security.KeyPair;
import java.security.KeyPairGenerator;
import java.security.Security;
import java.security.interfaces.RSAPublicKey;
import java.security.spec.RSAKeyGenParameterSpec;
import java.util.Arrays;
import java.util.Collections;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;
import javax.crypto.Cipher;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * The runtime's support pieces, each held to the run's determinism or its
 * isolation from the workload: the engine's console, directory listings,
 * weak identity tables, replay key pairs, run-only names, ambient handoff
 * keys, and the WIRE stores' lock order.
 */
public class RuntimeSupportTest {
    @Before
    @After
    public void reset() {
        Security.removeProvider("CausynthReplayKeys");
        RunNames.resetForTests();
        HandoffMint.resetForTests();
        Interactions.resetForTests();
    }

    /** A workload that captures {@code System.err} reads none of the
     *  engine's lines (a40h2's FSImage-851 test asserted on its captured
     *  error output and failed on the schedule's diagnostics). */
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
        assertEquals("", captured.toString());
    }

    /** A listing comes back sorted by name, whatever order the file system
     *  keeps (SYMBOL-SCOPE §4.5); one that cannot be listed stays null. */
    @Test
    public void everyListingIsSortedByName() throws Exception {
        File directory = Files.createTempDirectory("listings").toFile();
        try {
            String[] names = {"BP-10-127.0.0.1-3", "BP-9-127.0.0.1-7",
                "VERSION", "current"};
            File[] files = new File[names.length];
            for (int i = names.length - 1; i >= 0; i--) {
                files[i] = new File(directory, names[i]);
                files[i].createNewFile();
            }
            assertArrayEquals(names, Listings.list(directory));
            assertArrayEquals(names, Listings.list(directory, (d, n) -> true));
            assertArrayEquals(files, Listings.listFiles(directory));
            assertArrayEquals(files, Listings.listFiles(directory,
                    (FileFilter) f -> true));
            assertArrayEquals(files, Listings.listFiles(directory,
                    (FilenameFilter) (d, n) -> true));
            assertNull(Listings.list(new File(directory, "missing")));
        } finally {
            for (File file : directory.listFiles()) file.delete();
            directory.delete();
        }
    }

    /** The weak identity tables are keyed by identity, never keeping a key
     *  alive. */
    @Test
    public void keysAreObjectsNotValuesAndACollectedKeysEntryGoes() {
        WeakIdentityMap<Integer> map = new WeakIdentityMap<>();
        String one = new String("node");
        String other = new String("node");
        assertNull(map.put(one, 1));
        assertNull(map.putIfAbsent(other, 2));
        assertEquals(Integer.valueOf(1), map.putIfAbsent(one, 3));
        assertEquals(Integer.valueOf(1), map.get(one));
        assertEquals(Integer.valueOf(2), map.get(other));
        assertEquals(Integer.valueOf(1), map.put(one, 4));
        assertEquals(Integer.valueOf(4), map.remove(one));
        assertNull(map.get(one));
        assertNull(map.get(null));
        assertFalse(map.isEmpty());
        map.clear();
        assertTrue(map.isEmpty());

        WeakReference<Object> watched = putUnreferenced(map);
        for (int attempt = 0; attempt < 50 && watched.get() != null;
                attempt++) {
            System.gc();
            byte[][] pressure = new byte[16][];
            for (int index = 0; index < pressure.length; index++) {
                pressure[index] = new byte[1 << 20];
            }
        }
        assertNull("the key was never collected", watched.get());
        Object probe = new Object();
        for (int attempt = 0; attempt < 50 && !map.isEmpty(); attempt++) {
            map.get(probe);
            Thread.yield();
        }
        assertTrue(map.isEmpty());
    }

    private static WeakReference<Object> putUnreferenced(
            WeakIdentityMap<Integer> map) {
        Object key = new Object();
        map.put(key, 7);
        return new WeakReference<>(key);
    }

    /**
     * Installed, the JDK's RSA generator draws the pool's pairs one after
     * another, each a working pair, the same in every JVM; a size or an
     * exponent the pool has none of is the JDK's own search.
     */
    @Test(timeout = 60000L)
    public void anRsaKeyPairIsDrawnFromThePool() throws Exception {
        ReplayKeys.install();
        ReplayKeys.install();
        assertEquals("CausynthReplayKeys",
                Security.getProviders()[0].getName());
        KeyPairGenerator generator = KeyPairGenerator.getInstance("RSA");
        generator.initialize(2048);
        KeyPair first = generator.generateKeyPair();
        KeyPair second = generator.generateKeyPair();
        assertNotEquals(first.getPublic(), second.getPublic());
        for (KeyPair pair : new KeyPair[] {first, second}) {
            assertEquals(2048, ((RSAPublicKey) pair.getPublic()).getModulus()
                    .bitLength());
            Cipher rsa = Cipher.getInstance("RSA/ECB/PKCS1Padding");
            rsa.init(Cipher.ENCRYPT_MODE, pair.getPrivate());
            byte[] sealed = rsa.doFinal(new byte[] {1, 2, 3});
            rsa.init(Cipher.DECRYPT_MODE, pair.getPublic());
            assertArrayEquals(new byte[] {1, 2, 3}, rsa.doFinal(sealed));
        }
        KeyPairGenerator again = KeyPairGenerator.getInstance("RSA");
        again.initialize(new RSAKeyGenParameterSpec(2048,
                RSAKeyGenParameterSpec.F4));
        // The pool's third pair, then its fourth, then its first again.
        again.generateKeyPair();
        again.generateKeyPair();
        assertEquals(first.getPublic(), again.generateKeyPair().getPublic());
        KeyPairGenerator searched = KeyPairGenerator.getInstance("RSA");
        searched.initialize(new RSAKeyGenParameterSpec(1024,
                BigInteger.valueOf(3)));
        assertEquals(BigInteger.valueOf(3), ((RSAPublicKey) searched
                .generateKeyPair().getPublic()).getPublicExponent());
        searched.initialize(768);
        assertFalse(first.getPublic().equals(searched.generateKeyPair()
                .getPublic()));
    }

    /**
     * A store location keyed in names every run spells alike: the run-only
     * names an adapter stated as a node's become the node's name, the
     * longest first, the host and port inside a stated node name too; an
     * identity hash stays; one no adapter stated is left, and named once.
     */
    @Test
    public void aLocationKeysByItsNodesStatedNames() {
        RunNames.spelled("auto0/node0", "10.0.0.1:8983");
        RunNames.spelled("auto0/node1", "10.0.0.1:8983_solr");
        RunNames.spelled("auto0/node0", "72088256043548677");
        RunNames.spelled("auto0/node0", "72088256043548677");
        RunNames.spelled("auto0/node2", "0");
        RunNames.spelled("auto0/node3", "10.0.0.3:9000_solr");
        String[][] rows = {
            // location, key, the run-only name left unstated
            {"/live_nodes/10.0.0.1:8983_solr", "/live_nodes/{auto0/node1}", ""},
            {"/x/10.0.0.1:8983/y", "/x/{auto0/node0}/y", ""},
            {"/e/72088256043548677-core_node3-n_",
                "/e/{auto0/node0}-core_node3-n_", ""},
            {"/live_nodes/10.0.0.2:7000_solr", "/live_nodes/10.0.0.2:7000_solr",
                "10.0.0.2:7000"},
            {"/a/0/b", "/a/0/b", ""},
            {"/u/http://10.0.0.3:9000/solr", "/u/http://{auto0/node3}/solr",
                ""},
            {"/q/Task@1a2b", "/q/Task@1a2b", ""},
            {"/q/Task@3c4d", "/q/Task@3c4d", ""}};
        for (String[] row : rows) {
            RunNames.Keyed keyed = RunNames.key(row[0]);
            assertEquals(row[0], row[1], keyed.location);
            assertEquals(row[0], row[2], keyed.unnamed);
        }
        assertTrue(RunNames.firstUnstated("10.0.0.2:7000"));
        assertFalse(RunNames.firstUnstated("10.0.0.2:7000"));
    }

    /**
     * An ambient attach is keyed like a selected one: (port, consumer
     * occurrence, k-th attach of this element, element path).  k was the
     * constant 1, so the four block keys one heartbeat delivered were one
     * variable and a witness put every key under one key id (hdfs-17899
     * bug1, 17967 A, B, C).  A selected attach counts on the occurrence,
     * across the activations folding into it.
     */
    @Test
    public void eachElementOneOccurrenceReceivesIsItsOwnVariable() {
        String port = "XCH.1174244c.resp.block-key-id";
        String consumer = "hdfs-17899/target-dn#epoch0/region/REGION.16ba41cf"
                + "/ctx:Anchor:ab@HADOOP_IPC/heartbeat/idx:";
        String first = HandoffMint.ambientMintKey(port, consumer, "keyId");
        String second = HandoffMint.ambientMintKey(port, consumer, "keyId");
        String third = HandoffMint.ambientMintKey(port, consumer, "keyId");
        assertEquals("two elements, two variables", 3, new java.util.HashSet<>(
                Arrays.asList(first, second, third)).size());
        // Per element path and per consumer: another order mints the same.
        String expiry = HandoffMint.ambientMintKey(port, consumer,
                "expiryDate");
        String elsewhere = HandoffMint.ambientMintKey(port, consumer + "other",
                "keyId");
        HandoffMint.resetForTests();
        assertEquals(expiry, HandoffMint.ambientMintKey(port, consumer,
                "expiryDate"));
        assertEquals(elsewhere, HandoffMint.ambientMintKey(port,
                consumer + "other", "keyId"));
        assertEquals(first, HandoffMint.ambientMintKey(port, consumer,
                "keyId"));
        HandoffMint.resetForTests();
        for (int attach = 1; attach <= 4; attach++) {
            assertEquals(attach, HandoffMint.nextAttach(consumer, port,
                    "keyId"));
        }
        assertEquals("another consumer counts its own", 1,
                HandoffMint.nextAttach(consumer + "other", port, "keyId"));
    }

    /**
     * The two class monitors of the WIRE stores are taken in ONE order:
     * {@link Interactions} then {@link InteractionRefusals}.  On 11741
     * campaign #4 the reverse edge existed ({@code synchronized
     * InteractionRefusals.filedProducers}) and a focused replay hung forever
     * in a Java-level deadlock.  This races both paths and asks the VM what
     * that dump answered; with the {@code synchronized} put back it hangs
     * within the first thousands of iterations.
     */
    @Test
    public void theTwoStoresAreLockedInOneOrder() throws Exception {
        int filed = 2000;
        long overlapMs = 2000L;
        long joinMs = 4000L;
        String scanned = "";
        for (int k = 0; k < filed; k++) {
            Endpoint producer = producer(k);
            Interactions.sent("RPC", "correlation-" + k, "req", producer);
            scanned = producer.id();
        }
        String lookup = scanned;
        CountDownLatch ready = new CountDownLatch(2);
        CountDownLatch go = new CountDownLatch(1);
        AtomicInteger sending = new AtomicInteger();
        AtomicInteger rendering = new AtomicInteger();
        AtomicReference<Throwable> failure = new AtomicReference<>();
        // Both loop until the overlap elapses: a monitor is held for
        // microseconds, so what catches an order violation is overlap.
        Runnable[] paths = {() -> {
            // Holds Interactions, takes InteractionRefusals.
            long end = System.nanoTime() + overlapMs * 1000000L;
            for (int k = 0; System.nanoTime() < end; k++) {
                Endpoint producer = producer(filed + k);
                Interactions.sent("RPC", "live-" + k, "req", producer);
                Interactions.sharedProducer("RPC", "live-" + k, "req",
                        producer);
                sending.incrementAndGet();
            }
        }, () -> {
            // Takes Interactions from inside InteractionRefusals, owning
            // nothing of its own when it does.
            long end = System.nanoTime() + overlapMs * 1000000L;
            while (System.nanoTime() < end) {
                InteractionRefusals.endpoint(lookup);
                InteractionRefusals.components(lookup);
                rendering.incrementAndGet();
            }
        }};
        Thread[] threads = new Thread[paths.length];
        for (int at = 0; at < paths.length; at++) {
            Runnable path = paths[at];
            threads[at] = new Thread(() -> {
                try {
                    ready.countDown();
                    go.await();
                    path.run();
                } catch (Throwable thrown) {
                    failure.compareAndSet(null, thrown);
                }
            }, "interactions-" + at);
            // A test that deadlocks fails on its own clock.
            threads[at].setDaemon(true);
            threads[at].start();
        }
        ready.await();
        long deadline = System.currentTimeMillis() + overlapMs + joinMs;
        go.countDown();
        for (Thread thread : threads) {
            thread.join(Math.max(1L, deadline - System.currentTimeMillis()));
        }
        ThreadMXBean beans = ManagementFactory.getThreadMXBean();
        long[] deadlocked = beans.findDeadlockedThreads();
        StringBuilder where = new StringBuilder();
        if (deadlocked != null) {
            for (ThreadInfo info : beans.getThreadInfo(deadlocked, 4)) {
                if (info == null) continue;
                where.append('\n').append(info.getThreadName())
                        .append(" blocked on ").append(info.getLockName())
                        .append(" held by ").append(info.getLockOwnerName())
                        .append(' ').append(Arrays.toString(
                        info.getStackTrace()));
            }
        }
        assertNull("the WIRE stores deadlocked: " + where, deadlocked);
        if (failure.get() != null) {
            throw new AssertionError("a lock-order path threw", failure.get());
        }
        for (Thread thread : threads) {
            assertFalse(thread.getName() + " never left its loop: "
                    + sending.get() + "/" + rendering.get() + " iterations",
                    thread.isAlive());
        }
        assertTrue("both paths ran: a race of nothing proves nothing",
                sending.get() > 0 && rendering.get() > 0);
    }

    /** One producer endpoint, built the way the runtime builds one. */
    private static Endpoint producer(int k) {
        OccurrenceAddress occurrence = OccurrenceAddress.of(
                NodeId.of("dn" + (k % 4), 0), "REGION.wire",
                CausalContext.of(Role.CLIENT, "", k + 1),
                ExecutionIndex.of(Collections.singletonList(
                        Frame.of("BPServiceActor#offerService", k))));
        return Endpoint.of(occurrence, "XCH.wire.req.block-key-id",
                ExecutionIndex.of(Collections.singletonList(
                        Frame.of("Client#sendRpcRequest", k))), 0);
    }
}
