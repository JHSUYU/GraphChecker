package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import org.example.decoded.Decoded;
import org.junit.After;
import org.junit.Test;
import org.junit.runner.RunWith;

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
@RunWith(FreshStatics.class)
public class ProvenanceTest {
    private static final String PATH = "/collections/t/state.json";
    private static final LocationId STATE = LocationId.of(LocationKind.STORE,
            "SOLR_ZK", PATH);

    @After
    public void reset() {
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
}
