import java.util.LinkedHashMap;
import java.util.Map;

/** Exact scheduled handoff of one retained whole-map producer state. */
public final class RegionSharedMapProducerStateSmoke {
    private static final String EDGE = "EDGE.map-producer-state.smoke";

    private static final class Input {
        int value = 7;
    }

    public static void main(String[] args) {
        long session = System.openWorkloadSession();
        require(session > 0L, "workload session rejected: " + session);

        Map<Integer, Integer> producer =
                new LinkedHashMap<Integer, Integer>();
        require(System.startConcolicRegion(
                "REGION.map-producer", "TASK.map-producer") == 0L,
                "producer region rejected");
        require(System.selectSharedMapCarrier(producer) > 0L,
                "producer carrier rejected");
        Input input = new Input();
        System.symbolizeExactField(input, Input.class.getName(), "value", "I",
                "MAP.PRODUCER.VALUE");
        producer.put(Integer.valueOf(1), Integer.valueOf(input.value));

        long version = System.getCurrentSharedMapVersion(producer);
        require(version > 0L, "current producer state missing: " + version);

        Map<Integer, Integer> untouched =
                new LinkedHashMap<Integer, Integer>();
        String beforeLookup = System.getSharedMapVersions(untouched);
        require(System.getCurrentSharedMapVersion(untouched) < 0L,
                "untracked map unexpectedly had a current version");
        String afterLookup = System.getSharedMapVersions(untouched);
        require(beforeLookup.contains("\"selected\":false"), beforeLookup);
        require(afterLookup.contains("\"selected\":false"), afterLookup);
        require(System.finishConcolicRegion().contains("\"complete\":true"),
                "producer summary incomplete");

        require(System.startConcolicRegion(
                "REGION.map-consumer", "TASK.map-consumer") == 0L,
                "consumer region rejected");

        Map<Integer, Integer> rejected =
                new LinkedHashMap<Integer, Integer>();
        require(System.admitSharedMapVersion(
                rejected, Long.MAX_VALUE, EDGE) < 0L,
                "unknown producer version was admitted");
        String rejectedEvidence = System.getSharedMapVersions(rejected);
        require(rejectedEvidence.contains("\"selected\":false"),
                "refusal minted a destination carrier: " + rejectedEvidence);
        require(!rejectedEvidence.contains("\"versionKind\":\"INITIAL\""),
                "refusal minted destination INITIAL: " + rejectedEvidence);

        Map<Integer, Integer> missingEdge =
                new LinkedHashMap<Integer, Integer>();
        require(System.admitSharedMapVersion(missingEdge, version, "") < 0L,
                "empty selected edge was admitted");
        require(System.getSharedMapVersions(missingEdge)
                        .contains("\"selected\":false"),
                "edge refusal minted a destination carrier");

        Map<Integer, Integer> consumer =
                new LinkedHashMap<Integer, Integer>();
        consumer.put(Integer.valueOf(1), Integer.valueOf(input.value));
        long readEvent = System.admitSharedMapVersion(consumer, version, EDGE);
        require(readEvent > 0L, "exact producer state rejected: " + readEvent);

        Integer observed = consumer.get(Integer.valueOf(1));
        require(observed != null && observed.intValue() == input.value,
                "concrete replay map is not aligned");

        String evidence = System.getSharedMapVersions(consumer);
        require(evidence.contains("\"reason\":\"PLANNED_PRODUCER_STATE\""),
                evidence);
        require(evidence.contains("\"resolution\":\"EXACT\""), evidence);
        require(!evidence.contains("\"reason\":\"AMBIGUOUS_WRITERS\""),
                "admitted state was re-resolved: " + evidence);
        require(evidence.contains("\"selectedEdgeId\":\"" + EDGE + "\""),
                evidence);
        require(evidence.contains(
                "\"chosenFieldVersionId\":" + version), evidence);
        require(evidence.contains("MAP.PRODUCER.VALUE"), evidence);

        String ledger = System.getEventLedger();
        require(ledger.contains("\"detail\":\"PLANNED_PRODUCER_STATE\""),
                ledger);
        require(ledger.contains("\"edgeKind\":\"FIELD_READ_FROM\""),
                ledger);
        require(ledger.contains("\"beforeEventId\":" + version), ledger);
        require(ledger.contains("\"afterEventId\":" + readEvent), ledger);

        require(System.finishConcolicRegion().contains("\"complete\":true"),
                "consumer summary incomplete");
        require(System.closeWorkloadSession() == 0L,
                "workload session did not close");
        System.out.println("CAUSYNTH_SHARED_MAP_PRODUCER_STATE_SMOKE_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
