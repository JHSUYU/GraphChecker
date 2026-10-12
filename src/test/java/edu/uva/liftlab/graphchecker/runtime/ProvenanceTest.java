package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import org.example.decoded.Decoded;
import org.junit.After;
import org.junit.Test;

import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;

/**
 * IDENTITY §7.2: each application object a decode's product holds is the
 * version it was parsed from; a later product holding an older object
 * leaves it its own; values, lambdas and an inner object's outer one are
 * none.
 */
public class ProvenanceTest {
    private static final String PATH = "/collections/t/state.json";
    private static final LocationId STATE = LocationId.of(LocationKind.STORE,
            "SOLR_ZK", PATH);

    @After
    public void reset() {
        Provenance.resetForTests();
    }

    @Test
    public void everyObjectOfADecodeHoldsItsVersionAndTheFirstDecodeKeepsIt() {
        Decoded.Client client = new Decoded.Client();
        Decoded.Slice one = new Decoded.Slice("shard1", "active");
        Decoded.Collection first = new Decoded.Collection(client, one);
        List<Object> registered = Provenance.register(
                new Provenance.Version(STATE, PATH, 3L), first);
        Decoded.Slice two = new Decoded.Slice("shard2", "construction");
        // A later parse that still holds the first slice.
        Decoded.Collection later = new Decoded.Collection(client, one, two);
        Provenance.register(new Provenance.Version(STATE, PATH, 4L), later);
        Object[][] rows = {
            {"the collection, its slice, its inner object", 3,
                registered.size()},
            {"the collection", 3L, Provenance.of(first).version},
            {"its slice, found through the map, the array and the list", 3L,
                Provenance.of(one).version},
            {"a later product's own objects", 4L,
                Provenance.of(two).version},
            {"a later product leaves an older object its own", 3L,
                Provenance.of(one).version},
            {"the inner object", 3L, Provenance.of(first.inner).version}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
        assertSame("its location", STATE, Provenance.of(first).location);
        assertNull("a value is none", Provenance.of(one.state));
        assertNull("a lambda's capture is none", Provenance.of(client));
        assertNull("nor what it holds", Provenance.of(client.connection));
        assertNull("an object no decode made", Provenance.of(new Object()));
        assertNull("a class's constant is no decode's",
                Provenance.of(Decoded.Router.DEFAULT));
        assertEquals("the later product reached the first's slice: stated",
                1L, Provenance.shared());
    }

    /**
     * What a decode reaches but did not make is none of its product: what a
     * supplier hands over (another fetch's states); an object another
     * version's decode registered keeps that version, and is stated.
     */
    @Test
    public void aSuppliersStatesAreNoProductAndAnotherVersionsObjectIsStated() {
        Decoded.Slice fetched = new Decoded.Slice("replica", "active");
        Decoded.Collection collection = new Decoded.Collection(
                new Decoded.Client(), new Decoded.Slice("shard1", "active"));
        collection.states = new Decoded.States(fetched);
        Provenance.register(new Provenance.Version(STATE, PATH, 5L),
                collection);
        assertNull("the supplier's states", Provenance.of(fetched));
        assertEquals("nothing shared yet", 0L, Provenance.shared());
        assertEquals("the supplier and the constant router: skipped, stated",
                2L, Provenance.skipped());
        // A router a static table holds as a value is a constant too.
        Decoded.Collection implicit = new Decoded.Collection(
                new Decoded.Client(), new Decoded.Slice("shard9", "active"));
        implicit.router = Decoded.Router.ROUTERS.get("implicit");
        Provenance.register(new Provenance.Version(STATE, PATH, 6L),
                implicit);
        assertNull("the table's router", Provenance.of(implicit.router));
        assertEquals("skipped, stated", 3L, Provenance.skipped());
        LocationId aliases = LocationId.of(LocationKind.STORE, "SOLR_ZK",
                "/aliases.json");
        Decoded.Collection again = new Decoded.Collection(
                new Decoded.Client(), collection.slices.get("shard1"));
        Provenance.register(new Provenance.Version(aliases, "/aliases.json",
                2L), again);
        assertEquals("it keeps its version", 5L,
                Provenance.of(collection.slices.get("shard1")).version);
        assertEquals("and is stated", 1L, Provenance.shared());
        // A provenance site's read of an object no decode registered is
        // counted (and stated once per site); no receiver, no read.
        Provenance.unregistered("Guard#u3", new Object());
        Provenance.unregistered("Guard#u3", new Object());
        Provenance.unregistered("Guard#u3", null);
        assertEquals("unregistered reads", 2L, Provenance.unregistered());
    }

    /**
     * A decode waits for a write in flight at its path to file before it
     * names the version's life (review M5): a create's version 0 decoded
     * before its creator's hook ran names the new life, not the old one.
     */
    @Test
    public void aDecodeWaitsForTheCreateInFlightToNameItsLife()
            throws Exception {
        Object owner = new Object();
        MessageDoors.stored("SOLR_ZK", "/m5/race@0", owner, null);
        MessageDoors.stored("SOLR_ZK", "/m5/race@1", owner, null);
        java.util.concurrent.CountDownLatch open =
                new java.util.concurrent.CountDownLatch(1);
        java.util.concurrent.CountDownLatch file =
                new java.util.concurrent.CountDownLatch(1);
        Thread creator = new Thread(() -> {
            long store = MessageDoors.storing("SOLR_ZK", "/m5/race");
            open.countDown();
            try {
                file.await();
            } catch (InterruptedException ignored) {
                return;
            }
            MessageDoors.stored("SOLR_ZK", "/m5/race@0", owner, null);
            MessageDoors.storeEnded("SOLR_ZK", store);
        });
        creator.start();
        open.await();
        Decoded.Slice parsed = new Decoded.Slice("shard1", "active");
        Thread decoder = new Thread(() ->
                MessageDoors.decoded("SOLR_ZK", "/m5/race@0", parsed));
        decoder.start();
        Thread.sleep(200L);
        file.countDown();
        decoder.join();
        creator.join();
        assertEquals("/m5/race#2", Provenance.of(parsed).location.slot());
    }

    /**
     * SYMBOL-SCOPE §5.7: an object a constructor builds from a decoded
     * receiver it reads holds the receiver's version (a processor's copy of
     * its collection's read-only flag), once: it keeps the first, and a
     * second decode's is stated.
     */
    @Test
    public void aConstructorsCopyOfADecodedObjectHoldsItsVersion() {
        Decoded.Slice one = new Decoded.Slice("shard1", "active");
        Provenance.register(new Provenance.Version(STATE, PATH, 7L), one);
        Object processor = new Object();
        boolean[] derived = new boolean[1];
        assertEquals(7L, Provenance.observe(one, processor, derived).version);
        assertEquals("taken now", true, derived[0]);
        Decoded.Slice two = new Decoded.Slice("shard2", "active");
        Provenance.register(new Provenance.Version(STATE, PATH, 9L), two);
        derived[0] = false;
        Provenance.observe(two, processor, derived);
        assertEquals("the first kept", 7L, Provenance.of(processor).version);
        assertEquals("not taken again", false, derived[0]);
        assertEquals("a holder built from two decodes: stated", 1L,
                Provenance.shared());
        assertNull("an object no decode made derives nothing",
                Provenance.observe(new Object(), new Object(), derived));
    }
}
