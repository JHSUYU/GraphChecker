package edu.uva.liftlab.graphchecker.causynth;

import static org.junit.Assert.assertEquals;

import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import org.junit.Test;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.TreeSet;

public class RuntimeSelectedRegionFinalizerTest {
    @Test
    public void aClientsReadOrWritePairsAcrossNodesByObjectAlone() {
        Object[][] table = {
            {"auto0/master0#epoch0", "auto0/master0#epoch0", false, false, true},
            {"auto0/master0#epoch0", "auto0/rs0#epoch0", false, false, false},
            {"auto0/client0#epoch0", "auto0/master0#epoch0", true, false, true},
            {"auto0/master0#epoch0", "auto0/client0#epoch0", false, true, true},
            {"auto0/client0#epoch0", "auto1/client0#epoch0", true, true, true},
        };
        for (Object[] row : table) {
            assertEquals(row[0] + " read, " + row[1] + " wrote",
                    row[4], RuntimeSelectedRegionFinalizer.pairs(
                            (String) row[0], (String) row[1],
                            (Boolean) row[2], (Boolean) row[3]));
        }
    }

    private static final String MASTER = "auto0/master0#epoch0/region/";
    private static final String TURN = "/ctx:Anchor:m@HBASE_RPC/test/idx:";
    private static final String CLIENT = "auto0/client0#epoch0/region/"
            + "REGION.send/ctx:Root:CLIENT/test#1/idx:";

    @Test
    public void aDoorEarlierInItsOwnTurnIsAControlProducer() {
        String writer = MASTER + "REGION.cached" + TURN;
        String put = MASTER + "REGION.put" + TURN;
        String later = MASTER + "REGION.later" + TURN;
        String elsewhere = MASTER + "REGION.put/ctx:Anchor:x@HBASE_RPC/test"
                + "/idx:";
        Object[][] table = {
            {200L, null, ids(CLIENT, put), "[earlier in turn, own turn]"},
            {120L, null, ids(CLIENT), "[own turn]"},
            {120L, Arrays.asList(120L, 400L), ids(CLIENT, put, later),
                    "[earlier in turn]"},
            {null, null, ids(CLIENT), "[own turn]"},
        };
        for (Object[] row : table) {
            StaticProgram program = new StaticProgram();
            if (row[0] != null) {
                Map<String, Object> served = activation((Long) row[0]);
                if (row[1] != null) {
                    served.put(RuntimeSelectedRegionFinalizer
                            .SHARED_ADDRESS_ROOT_CALLS, row[1]);
                }
                program.activations.put(writer, served);
            }
            program.activations.put(put, activation(150L));
            program.activations.put(later, activation(300L));
            program.activations.put(elsewhere, activation(100L));
            RecordedMessages messages = new RecordedMessages(Arrays.asList(
                    ScheduleEvent.of(1L, ScheduleEvent.Kind.SEND,
                            "auto0/client0#epoch0|Root:CLIENT/test#1",
                            "HBASE_RPC#REQUEST:MasterService.CreateNamespace",
                            0, OccurrenceAddress.parse(CLIENT).id(), "m"),
                    ScheduleEvent.of(2L, ScheduleEvent.Kind.RECV,
                            "auto0/master0#epoch0|Anchor:m@HBASE_RPC/test",
                            "HBASE_RPC#REQUEST", 0, "", "")));
            String label = "writer's root call " + row[0] + " " + row[1];
            assertEquals(label, row[2], new TreeSet<>(
                    RuntimeSelectedRegionFinalizer.doorsOf(messages, program,
                            writer)).toString());
            TreeSet<String> gaps = new TreeSet<>();
            for (Map<String, Object> gap : program.planGaps) {
                String subject = String.valueOf(gap.get("subject"));
                gaps.add(subject.substring(subject.indexOf(' ') + 1));
            }
            assertEquals(label, row[3], gaps.toString());
        }
    }

    private static Map<String, Object> activation(long rootCall) {
        Map<String, Object> activation = new LinkedHashMap<>();
        activation.put("rootCallId", rootCall);
        return activation;
    }

    private static String ids(String... addresses) {
        TreeSet<String> ids = new TreeSet<>();
        for (String address : addresses) {
            ids.add(OccurrenceAddress.parse(address).id());
        }
        return ids.toString();
    }
}
