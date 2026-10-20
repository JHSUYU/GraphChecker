package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import org.junit.Test;
import org.junit.runner.RunWith;

@RunWith(FreshStatics.class)
public class MessageDoorsTest {
    private static final String ZK = "STORE";

    private static void write(String key) {
        String path = MessageDoors.location(key);
        if (key.endsWith("@" + MessageDoors.TOMBSTONE)) {
            MessageDoors.deleted(ZK, path, null);
        } else {
            MessageDoors.stored(ZK, key, null, null);
        }
    }

    @Test
    public void anAbsentReadNamesTheTombstoneOfThePathsCurrentLifeOnly() {
        String[][] rows = {
                {"", "-1", "/p"},
                {"/p@0", "-1", "/p"},
                {"/p@0 /p@" + MessageDoors.TOMBSTONE, "" + MessageDoors.TOMBSTONE,
                        "/p"},
                {"/p@0 /p@" + MessageDoors.TOMBSTONE + " /p@0", "-1", "/p#2"},
                {"/p@0 /p@" + MessageDoors.TOMBSTONE + " /p@0 /p@"
                        + MessageDoors.TOMBSTONE, "" + MessageDoors.TOMBSTONE,
                        "/p#2"},
                {"/q@0 /q@" + MessageDoors.TOMBSTONE, "-1", "/p"},
        };
        for (String[] row : rows) {
            ((Map<?, ?>) Fixtures.get(MessageDoors.class, "LIVES")).clear();
            for (String key : row[0].split(" ")) {
                if (!key.isEmpty()) write(key);
            }
            assertEquals(row[0], Long.parseLong(row[1]),
                    MessageDoors.absentVersion(ZK, "/p"));
            assertEquals(row[0], row[2], MessageDoors.livePath(ZK,
                    "/p@" + MessageDoors.TOMBSTONE));
        }
        assertFalse(MessageDoors.absent(ZK, "/never", "getData", null));
    }

    @Test
    public void aChildrenListingTakesTheNewestFiledCreateNotYetDelivered() {
        @SuppressWarnings("unchecked")
        Map<String, Long> filings = (Map<String, Long>) Fixtures.get(
                MessageDoors.class, "FILINGS");
        filings.put(ZK + "\n/a/x@0", 3L);
        filings.put(ZK + "\n/a/y@0", 7L);
        filings.put(ZK + "\n/a/z@0", 5L);
        Object[][] rows = {
                {Arrays.asList("/a/x@0", "/a/y@0", "/a/z@0"),
                        Collections.emptySet(), "/a/y@0"},
                {Arrays.asList("/a/x@0", "/a/y@0", "/a/z@0"),
                        new HashSet<>(Arrays.asList("/a/y@0")), "/a/z@0"},
                {Arrays.asList("/a/x@0", "/a/w@0"),
                        Collections.emptySet(), "/a/x@0"},
                {Arrays.asList("/a/w@0"), Collections.emptySet(), null},
        };
        for (Object[] row : rows) {
            @SuppressWarnings("unchecked")
            String newest = MessageDoors.newestFiled(ZK,
                    (java.util.List<String>) row[0],
                    (java.util.Set<String>) row[1]);
            assertEquals(String.valueOf(row[0]), row[2], newest);
        }
        assertNull(MessageDoors.current());
    }
}
