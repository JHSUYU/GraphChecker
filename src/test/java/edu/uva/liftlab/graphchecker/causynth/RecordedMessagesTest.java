package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
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

    /**
     * A message sent in no region occurrence names where it was sent from,
     * the context PLAN states its unreachable doors in
     * (DOOR_SEND_OUTSIDE_REGION: solr-bugs-migrate-buffer-leak SG2); one an
     * occurrence sent, or none, names nothing.
     */
    @Test
    public void aMessageSentInNoRegionNamesWhereItWasSent() {
        RecordedMessages messages = new RecordedMessages(SCHEDULE);
        String[][] rows = {
            {"sent by an occurrence", "Anchor:e1@HADOOP_IPC/hb", null},
            {"sent in no region", "Anchor:e2@HADOOP_IPC/hb",
                "s/n1#epoch0|Anchor:e1@HADOOP_IPC/hb"},
            {"started by no message", "Root:CLIENT/hb#1", null},
        };
        for (String[] row : rows) {
            ContextShape.Stance from = messages.sentOutsideRegion(
                    OccurrenceAddress.parse("s/n1#epoch0/region/REGION.h/ctx:"
                            + row[1] + "/idx:"));
            assertEquals(row[0], row[2], from == null ? null : from.render());
        }
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
