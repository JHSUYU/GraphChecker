package edu.uva.liftlab.graphchecker.causynth;

import static org.junit.Assert.assertEquals;

import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import org.junit.Test;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
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

    @Test
    public void onlyACaseThatDeclaresItCrossesAnExportGuardToAnotherTarget() {
        Object[][] table = {
            {"an export guard's demand, declared", true, false, true, true},
            {"the same, the writer's address shared", true, true, true, false},
            {"an export guard's demand, undeclared", true, false, false, false},
            {"any other demand, declared", false, false, true, false},
        };
        for (Object[] row : table) {
            assertEquals((String) row[0], row[4],
                    RuntimeSelectedRegionFinalizer.exportGuardWriter(
                            (Boolean) row[1], (Boolean) row[2],
                            (Boolean) row[3]));
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

    @Test
    public void aPlannedOccurrenceIsAloneInAContextTheRecordingOpenedItsRegionInOnce() {
        String region = "auto0/peer2#epoch0/region/REGION.lead/ctx:";
        String turn = region + "Root:CLIENT/test#1/idx:a.W#run#292@4";
        String again = region + "Root:CLIENT/test#1/idx:a.W#run#292@5";
        String other = region + "Root:CLIENT/test#2/idx:a.W#run#292@1";
        Map<String, Map<String, Object>> instances = new LinkedHashMap<>();
        for (String address : Arrays.asList(turn, again, other)) {
            instances.put(address, new LinkedHashMap<String, Object>());
        }
        RuntimeSelectedRegionFinalizer.stateShapes(instances,
                Arrays.asList(turn, other),
                context -> ContextShape.of(context, producer -> null));
        Object[][] table = {
            {turn, false, ids(again, other)},
            {other, true, ids(turn, again)},
        };
        for (Object[] row : table) {
            Map<String, Object> planned = instances.get((String) row[0]);
            assertEquals((String) row[0], row[1], planned.get(
                    RuntimeSelectedRegionFinalizer.ALONE_IN_CONTEXT));
            @SuppressWarnings("unchecked")
            List<String> beside = (List<String>) planned.get(
                    RuntimeSelectedRegionFinalizer.RECORDED_BESIDE);
            assertEquals((String) row[0], row[2],
                    new TreeSet<>(beside).toString());
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
