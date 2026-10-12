package edu.uva.liftlab.graphchecker.explore;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

/**
 * The schedule a focused replay is handed: the discovering session's order,
 * cut at the target -- the prefix before the cut, and the rest after it,
 * whose timeouts still hold.
 */
public class SchedulePrefixTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void theCutSplitsTheOrderIntoThePrefixAndTheRest()
            throws Exception {
        Path iteration = folder.newFolder("iteration").toPath();
        SessionDir session = SessionDir.of(iteration, "s1");
        Files.createDirectories(session.schedule().getParent());
        List<JsonObject> rows = new ArrayList<JsonObject>();
        rows.add(row(0, ScheduleEvent.Kind.SEND, "a", ""));
        rows.add(row(1, ScheduleEvent.Kind.WAKE, "tick.nn", ""));
        JsonObject mark = new JsonObject();
        mark.addProperty("mark", "OCC.focus");
        mark.addProperty("at", 2L);
        rows.add(mark);
        rows.add(row(2, ScheduleEvent.Kind.RECV, "b", "OCC.focus"));
        rows.add(row(3, ScheduleEvent.Kind.WAKE, "tick.dn", ""));
        // The source run was cut at its witness, and was one invocation of
        // a parameterized test.
        rows.add(RowCodec.writeScheduleMark(ScheduleEvent.WITNESS, 4L));
        rows.add(0, RowCodec.writeScheduleInvocation("m[1](null)"));
        RowCodec.writeJsonl(session.schedule(), rows);
        Path out = folder.newFolder("worker").toPath();

        SchedulePrefix.Cut cut = SchedulePrefix.write(iteration, "s1",
                Collections.singletonList("OCC.focus"), true, out);

        assertEquals(Arrays.asList("a", "tick.nn"),
                sites(out.resolve(SchedulePrefix.FILE)));
        assertEquals("the rest is handed too: its timeouts hold",
                Arrays.asList("b", "tick.dn"),
                sites(out.resolve(SchedulePrefix.REST_FILE)));
        JsonObject stated = cut.toJson();
        assertEquals(2, stated.get("events").getAsInt());
        assertEquals(2, stated.get("rest").getAsInt());
        assertEquals(4, stated.get("of").getAsInt());
        assertTrue(stated.get("cutAtFocus").getAsBoolean());
        assertTrue("the order ends at the source's witness, and the replay "
                + "reads that off its rest", stated.get("endsAtWitness")
                .getAsBoolean() && SessionReader.readScheduleMarks(out.resolve(
                SchedulePrefix.REST_FILE)).containsKey(ScheduleEvent.WITNESS));
        assertEquals("the replay checks it runs the source's invocation",
                "m[1](null)", SessionReader.readScheduleInvocation(out.resolve(
                        SchedulePrefix.REST_FILE)).get("of").getAsString());
        assertEquals("the replay reads the rest under the name it looks for",
                edu.uva.liftlab.graphchecker.runtime.ScheduleLog.SUFFIX_FILE,
                SchedulePrefix.REST_FILE);

        // A CONFIRM run holds no prefix: all of it is rest, WAKEs included.
        Path unheld = folder.newFolder("confirm").toPath();
        SchedulePrefix.write(iteration, "s1",
                Collections.singletonList("OCC.focus"), false, unheld);
        assertEquals(Collections.emptyList(),
                sites(unheld.resolve(SchedulePrefix.FILE)));
        assertEquals(Arrays.asList("a", "tick.nn", "b", "tick.dn"),
                sites(unheld.resolve(SchedulePrefix.REST_FILE)));
    }

    /**
     * A prefix cut before a row's event ({@code ScheduleEvent#vmEvent}, the
     * order rows' seqs are in) ends at the first event made at or after it,
     * whatever occurrence: a decode in role work is cut before itself.
     */
    @Test
    public void theCutStopsBeforeTheFirstEventAtOrAfterARowsEvent()
            throws Exception {
        Path iteration = folder.newFolder("iteration").toPath();
        SessionDir session = SessionDir.of(iteration, "s1");
        Files.createDirectories(session.schedule().getParent());
        List<JsonObject> rows = new ArrayList<JsonObject>();
        long[] made = {10L, 20L, 0L, 30L, 40L};
        for (int index = 0; index < made.length; index++) {
            rows.add(RowCodec.writeScheduleEvent(ScheduleEvent.of(index,
                    ScheduleEvent.Kind.SEND, "node|Root:X", "e" + index, 0,
                    "ROLE.X", "", made[index])));
        }
        RowCodec.writeJsonl(session.schedule(), rows);
        Path out = folder.newFolder("worker").toPath();
        SchedulePrefix.Cut cut = SchedulePrefix.write(iteration, "s1",
                Collections.<String>emptyList(), 30L, true, out);
        assertEquals(Arrays.asList("e0", "e1", "e2"),
                sites(out.resolve(SchedulePrefix.FILE)));
        assertEquals(Arrays.asList("e3", "e4"),
                sites(out.resolve(SchedulePrefix.REST_FILE)));
        assertTrue(cut.toJson().get("cutAtFocus").getAsBoolean());
        assertEquals("the event survives the codec", 30L, SessionReader
                .readSchedule(out.resolve(SchedulePrefix.REST_FILE)).get(0)
                .vmEvent());
    }

    private static JsonObject row(long seq, ScheduleEvent.Kind kind,
                                  String site, String occurrence) {
        return RowCodec.writeScheduleEvent(ScheduleEvent.of(seq, kind,
                "node|Root:X", site, 0, occurrence));
    }

    private static List<String> sites(Path file) throws Exception {
        List<String> sites = new ArrayList<String>();
        for (ScheduleEvent event : SessionReader.readSchedule(file)) {
            sites.add(event.site());
        }
        return sites;
    }
}
