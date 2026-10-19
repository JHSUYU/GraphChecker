package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;

import static org.junit.Assert.assertEquals;

public class RecordedMessagesTest {
    private static final String TARGET = "auto0/client0#epoch0/region/REGION.t"
            + "/ctx:Root:CLIENT/test#1/idx:";

    @Test
    public void theReadersOfTheRepliesToWhatAnOccurrenceSentAreItsReplyLegs() {
        OccurrenceAddress target = OccurrenceAddress.parse(TARGET);
        String scanReader = "scan-reply-reader";
        String casReader = "cas-reply-reader";
        String sameThread = "sync-caller-after-reply";
        List<ScheduleEvent> schedule = new ArrayList<>(Arrays.asList(
                send(0, "auto0/client0#epoch0|Root:CLIENT/test#1",
                        "HBASE_RPC#REQUEST:ClientService.Scan", target.id(),
                        "scan"),
                send(1, "auto0/rs0#epoch0|Anchor:scan@HBASE_RPC/test",
                        "HBASE_RPC#RESPONSE", "", "scan-reply"),
                send(2, "auto0/client0#epoch0|Anchor:scan-reply@HBASE_RPC/test",
                        "HBASE_RPC#REQUEST:ClientService.Mutate", scanReader,
                        "cas"),
                send(3, "auto0/rs0#epoch0|Anchor:cas@HBASE_RPC/test",
                        "HBASE_RPC#RESPONSE", "", "cas-reply"),
                send(4, "auto0/rs0#epoch0|Anchor:cas@HBASE_RPC/test",
                        "HBASE_RPC#REQUEST:ClientService.Get", "server-work",
                        "server-call"),
                send(5, "auto0/rs1#epoch0|Anchor:server-call@HBASE_RPC/test",
                        "HBASE_RPC#RESPONSE", "", "server-call-reply"),
                send(6, "auto0/client0#epoch0|Root:CLIENT/test#2",
                        "HADOOP_IPC#REQUEST:ClientProtocol.mkdirs",
                        "another-request", "unrelated")));
        Map<String, List<String>> readers = new HashMap<>();
        readers.put("scan-reply", Arrays.asList(scanReader));
        readers.put("cas-reply", Arrays.asList(casReader, sameThread));
        readers.put("server-call-reply", Arrays.asList("server-reply-reader"));
        readers.put("unrelated", Arrays.asList("unrelated-reader"));
        Object[][] table = {
            {target, "[cas-reply-reader, scan-reply-reader, "
                    + "sync-caller-after-reply]"},
            {OccurrenceAddress.parse(TARGET.replace("REGION.t", "REGION.u")),
                    "[]"},
        };
        RecordedMessages messages = new RecordedMessages(schedule);
        for (Object[] row : table) {
            assertEquals(row[1], new TreeSet<>(messages.replyLegsOf(
                    (OccurrenceAddress) row[0], readers)).toString());
        }
    }

    private static ScheduleEvent send(long seq, String context, String site,
                                      String occurrence, String endpoint) {
        return ScheduleEvent.of(seq, ScheduleEvent.Kind.SEND, context, site, 0,
                occurrence, endpoint);
    }
}
