package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import org.junit.Test;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;

import static org.junit.Assert.assertEquals;

/**
 * IDENTITY §4, §8: what the recording's schedule says of a message -- the
 * doors of the one that started an occurrence, and the shape of a context
 * over the stances its senders stood in.
 */
public class RecordedMessagesTest {
    private static final List<ScheduleEvent> SCHEDULE = Arrays.asList(
            ScheduleEvent.of(0, ScheduleEvent.Kind.SEND,
                    "s/n0#epoch0|Root:CLIENT/hb#1", "HADOOP_IPC#REQUEST",
                    0, "sender", "e1"),
            ScheduleEvent.of(1, ScheduleEvent.Kind.RECV,
                    "s/n1#epoch0|Anchor:e1@HADOOP_IPC/hb",
                    "HADOOP_IPC#REQUEST", 0, "receiver"),
            // a role's send: no occurrence holds its door
            ScheduleEvent.of(2, ScheduleEvent.Kind.SEND,
                    "s/n1#epoch0|Anchor:e1@HADOOP_IPC/hb",
                    "HADOOP_IPC#RESPONSE", 0, "", "e2"));

    @Test
    public void aMessagesDoorsAreItsSenderAndItsReceivers() {
        RecordedMessages messages = new RecordedMessages(SCHEDULE);
        Object[][] rows = {
            {"started by message e1", "Anchor:e1@HADOOP_IPC/hb",
                set("sender", "receiver")},
            {"started by a role's message", "Anchor:e2@HADOOP_IPC/hb", set()},
            {"started by no message", "Root:CLIENT/hb#1", set()},
        };
        for (Object[] row : rows) {
            OccurrenceAddress occurrence = OccurrenceAddress.parse(
                    "s/n1#epoch0/region/REGION.h/ctx:" + row[1] + "/idx:");
            assertEquals((String) row[0], row[2],
                    messages.doorsOf(occurrence));
        }
    }

    /** IDENTITY §7.2: a message has a door in every occurrence of the turn
     *  that sent it, and of a turn that took it in at its root, no
     *  occurrence open -- not of a turn standing on it, which it started. */
    @Test
    public void aMessageHasItsSendingTurnsDoorsAndThoseOfTurnsThatTookItIn() {
        RecordedMessages messages = new RecordedMessages(Arrays.asList(
                SCHEDULE.get(0), SCHEDULE.get(1), SCHEDULE.get(2),
                ScheduleEvent.of(3, ScheduleEvent.Kind.RECV,
                        "s/n2#epoch0|Root:QUEUE#4", "SOLR_ZK#REQUEST", 0, "",
                        "e1"),
                // a handler's turn stands on the message: no door of it
                ScheduleEvent.of(4, ScheduleEvent.Kind.RECV,
                        "s/n3#epoch0|Anchor:e1@HADOOP_IPC/hb",
                        "HADOOP_IPC#REQUEST", 0, "")));
        Object[][] rows = {
            {"sent in an occurrence, taken in at a root",
                "Anchor:e1@HADOOP_IPC/hb", set("s/n2#epoch0|Root:QUEUE#4",
                        "s/n0#epoch0|Root:CLIENT/hb#1")},
            {"sent at a root", "Anchor:e2@HADOOP_IPC/hb",
                set("s/n1#epoch0|Anchor:e1@HADOOP_IPC/hb")},
            {"started by no message", "Root:CLIENT/hb#1", set()},
        };
        for (Object[] row : rows) {
            OccurrenceAddress occurrence = OccurrenceAddress.parse(
                    "s/n1#epoch0/region/REGION.h/ctx:" + row[1] + "/idx:");
            assertEquals((String) row[0], row[2],
                    messages.doorStancesOf(occurrence));
        }
        // The handler's turn is what e1 started: no door, a cut its caller
        // names (review M4).
        assertEquals(set("s/n3#epoch0|Anchor:e1@HADOOP_IPC/hb"),
                messages.handlerStancesOf(OccurrenceAddress.parse(
                        "s/n1#epoch0/region/REGION.h/ctx:Anchor:e1@HADOOP_IPC"
                                + "/hb/idx:")));
    }

    /** A batching turn (an Overseer state writer flushing several queue
     *  items at once) is started by every item it took in: each item's
     *  sender is a door of its occurrences, not only the first's. */
    @Test
    public void aBatchingTurnIsStartedByEveryItemItTookIn() {
        RecordedMessages messages = new RecordedMessages(Arrays.asList(
                SCHEDULE.get(0),
                ScheduleEvent.of(1, ScheduleEvent.Kind.SEND,
                        "s/n0#epoch0|Root:CLIENT/hb#2", "SOLR_ZK#REQUEST", 0,
                        "second sender", "e3"),
                ScheduleEvent.of(2, ScheduleEvent.Kind.RECV,
                        "s/n2#epoch0|Root:QUEUE#4", "SOLR_ZK#REQUEST", 0,
                        "", "e1"),
                ScheduleEvent.of(3, ScheduleEvent.Kind.RECV,
                        "s/n2#epoch0|Root:QUEUE#4", "SOLR_ZK#REQUEST", 0,
                        "", "e3")));
        OccurrenceAddress flush = OccurrenceAddress.parse(
                "s/n2#epoch0/region/REGION.w/ctx:Root:QUEUE#4/idx:");
        assertEquals(set("sender", "second sender"), messages.doorsOf(flush));
        assertEquals(set("s/n2#epoch0|Root:QUEUE#4",
                "s/n0#epoch0|Root:CLIENT/hb#1",
                "s/n0#epoch0|Root:CLIENT/hb#2"),
                messages.doorStancesOf(flush));
    }

    @Test
    public void aShapeFollowsEverySenderTheScheduleStates() {
        assertEquals(Arrays.asList("HADOOP_IPC/hb@s/n1#epoch0",
                "HADOOP_IPC/hb@s/n0#epoch0", "Root:CLIENT/hb"),
                new RecordedMessages(SCHEDULE).shape(
                        CausalContext.parse("Anchor:e2@HADOOP_IPC/hb")));
    }

    private static HashSet<String> set(String... values) {
        return new HashSet<>(Arrays.asList(values));
    }
}
