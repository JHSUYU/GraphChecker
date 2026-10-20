package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
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
                    (OccurrenceAddress) row[0], Collections.<String>emptyList(),
                    readers)).toString());
        }
    }

    @Test
    public void aRequestSentByWorkStandingUnderAnOccurrenceIsItsRequest() {
        String context = "auto0/client0#epoch0/region/REGION.%s"
                + "/ctx:Root:CLIENT/%s/idx:<a.Test: void run()>@%s"
                + "/<a.Table: void lock()>@0%s";
        String under = "/<a.Futures: void addListener()>#u3:a.Caller.doCall@0"
                + "/<a.Rpc: void callMethod()>@0";
        OccurrenceAddress target = OccurrenceAddress.parse(
                String.format(context, "t", "test#1", "1", ""));
        Object[][] table = {
            {"a continuation it registered", "test#1", "1", under, true},
            {"its own context, another index", "test#1", "10", under, false},
            {"another context, its index", "test#2", "1", under, false},
            {"its own address in another region", "test#1", "1", "", false},
        };
        for (Object[] row : table) {
            OccurrenceAddress sender = OccurrenceAddress.parse(String.format(
                    context, "call", row[1], row[2], row[3]));
            List<ScheduleEvent> schedule = Arrays.asList(
                    send(0, "auto0/client0#epoch0|Root:CLIENT/" + row[1],
                            "HBASE_RPC#REQUEST:ClientService.Mutate",
                            sender.id(), "cas"),
                    send(1, "auto0/rs0#epoch0|Anchor:cas@HBASE_RPC/test",
                            "HBASE_RPC#RESPONSE", "", "cas-reply"));
            Map<String, List<String>> readers = new HashMap<>();
            readers.put("cas-reply", Arrays.asList("cas-reply-reader"));
            assertEquals((String) row[0], (Boolean) row[4]
                    ? "[cas-reply-reader]" : "[]", new TreeSet<>(
                    new RecordedMessages(schedule).replyLegsOf(target,
                            Arrays.asList(sender.render()), readers))
                    .toString());
        }
    }

    private static ScheduleEvent send(long seq, String context, String site,
                                      String occurrence, String endpoint) {
        return ScheduleEvent.of(seq, ScheduleEvent.Kind.SEND, context, site, 0,
                occurrence, endpoint);
    }
}
