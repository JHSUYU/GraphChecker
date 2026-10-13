package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * A planted SessionExpired takes only as a real expiry of the door's session
 * at its server ({@link Sessions#expires}, the system's expirer): with none,
 * or one that knows no session of the door's owner, or one that fails, the
 * world is impossible, refused by name, and the call's own result stands.
 */
public class PlantedSessionExpiryTest {
    private static final String MARKER =
            "FAULT:ZOOKEEPER:WRITE:KeeperException$SessionExpiredException";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Before
    public void openSession() throws Exception {
        RowRuntime.resetForTests();
        Sessions.resetForTests();
        Path results = folder.getRoot().toPath().resolve("iteration-0000")
                .resolve("seed-result").resolve(
                        "concolic_region_results.jsonl");
        Files.createDirectories(results.getParent());
        RowRuntime.configure(results);
    }

    @After
    public void clear() {
        Sessions.resetForTests();
        RowRuntime.resetForTests();
    }

    @Test
    public void aSessionExpiryIsPlantedOnlyWhereTheExpirerMakesItReal()
            throws Exception {
        Object client = new Object();
        // No expirer: refused.
        assertFalse(Sessions.expires(client, MARKER));
        // One that expires the owner's session: the plant takes, the owner
        // is the one it was asked about.
        List<Object> expired = new ArrayList<>();
        Sessions.expirer(owner -> expired.add(owner));
        assertTrue(Sessions.expires(client, MARKER));
        assertEquals(1, expired.size());
        assertTrue(expired.get(0) == client);
        // One that knows no session of it, and one that fails: refused.
        Sessions.expirer(owner -> false);
        assertFalse(Sessions.expires(null, MARKER));
        Sessions.expirer(owner -> {
            throw new IllegalStateException("server gone");
        });
        assertFalse(Sessions.expires(client, MARKER));
        List<GapRow> gaps = RowCodec.readAll(SessionDir.of(folder.getRoot()
                        .toPath().resolve("iteration-0000"),
                RowRuntime.sessionId()).gaps(), RowCodec::readGap);
        String[] why = {"no system expirer is registered",
            "knows no session of a static door", "failed: java.lang"};
        assertEquals(why.length, gaps.size());
        for (int at = 0; at < why.length; at++) {
            assertEquals(GapKind.ASSIGNMENT_UNPLANTED, gaps.get(at).kind());
            assertEquals(GapClass.BLOCKING, gaps.get(at).cls());
            assertTrue(gaps.get(at).detail(),
                    gaps.get(at).detail().contains(why[at]));
            assertTrue(gaps.get(at).subject().startsWith(MARKER));
        }
    }
}
