/** Exact scheduled handoff of retained scalar/reference field versions. */
public final class RegionSharedFieldProducerStateSmoke {
    private static final String BOOL_EDGE = "EDGE.field.bool";
    private static final String REF_EDGE = "EDGE.field.ref";
    private static final String NULL_EDGE = "EDGE.field.null";
    private static final String CANCEL_EDGE = "EDGE.field.cancel";
    private static final String SAME_LOCATION_EDGE =
            "EDGE.field.same-location";
    private static final String NESTED_SOURCE =
            "SOURCE.field.same-location.nested";

    private static final class Ref {
        int value;

        Ref(int value) {
            this.value = value;
        }

        int getValue() {
            return value;
        }
    }

    private static final class IntSink {
        int value;
    }

    private static final class DataKeyShape {
        int keyId;
        String pool;
        byte[] nonce;
        byte[] key;
        long expiry;
        String algorithm;

        DataKeyShape(int keyId, String pool, byte[] nonce, byte[] key,
                     long expiry, String algorithm) {
            this.keyId = keyId;
            this.pool = pool;
            this.nonce = nonce;
            this.key = key;
            this.expiry = expiry;
            this.algorithm = algorithm;
        }
    }

    private static final class Producer {
        boolean needKeyUpdate = true;
        Ref currentKey = new Ref(7);
        Ref nullableKey;
    }

    private static final class Consumer {
        boolean needKeyUpdate;
        Ref currentKey;
        Ref nullableKey;
    }

    private static final class ObjectConsumer {
        Object currentKey;
    }

    public static void main(String[] args) {
        long session = System.openWorkloadSession();
        require(session > 0L, "workload session rejected: " + session);

        Producer producer = new Producer();
        require(System.startConcolicRegion(
                "REGION.field-producer", "TASK.field-producer") == 0L,
                "producer region rejected");
        require(System.selectSharedFieldCarrier(
                producer, Producer.class.getName(), "needKeyUpdate", "Z")
                > 0L, "boolean producer carrier rejected");
        require(System.selectSharedFieldCarrier(
                producer, Producer.class.getName(), "currentKey", refDesc())
                > 0L, "reference producer carrier rejected");
        require(System.selectSharedFieldCarrier(
                producer, Producer.class.getName(), "nullableKey", refDesc())
                > 0L, "null producer carrier rejected");
        System.symbolizeExactField(producer.currentKey, Ref.class.getName(),
                "value", "I", NESTED_SOURCE);

        // Publish a concrete WRITE, not a symbolic discovery variable.
        producer.needKeyUpdate = true;

        long boolVersion = pureCurrentVersion(
                producer, "needKeyUpdate", "Z");
        long refVersion = pureCurrentVersion(
                producer, "currentKey", refDesc());
        long nullVersion = pureCurrentVersion(
                producer, "nullableKey", refDesc());
        require(System.finishConcolicRegion().contains("\"complete\":true"),
                "producer summary incomplete");

        require(System.startConcolicRegion(
                "REGION.field-consumer", "TASK.field-consumer") == 0L,
                "consumer region rejected");

        // A producer and consumer can share the very same Java state in one
        // workload session (the HDFS BlockTokenSecretManager is such a
        // carrier).  Its slot already contains the retained producer
        // expression and is already a selected location.  Exact admission
        // must attest that version instead of mistaking it for a conflicting
        // consumer-local symbolic input.
        require(System.admitSharedFieldVersion(
                producer, Producer.class.getName(), "currentKey", refDesc(),
                refVersion, SAME_LOCATION_EDGE) == refVersion,
                "same-location reference version rejected");
        Ref sameLocationRef = producer.currentKey;
        require(sameLocationRef != null && sameLocationRef.value == 7,
                "same-location concrete reference diverged");
        IntSink sameLocationSink = new IntSink();
        sameLocationSink.value = sameLocationRef.getValue();
        String nested = System.getSymbolicFieldExpression(
                sameLocationSink, IntSink.class.getName(), "value", "I",
                Integer.valueOf(sameLocationSink.value));
        require(nested.contains(NESTED_SOURCE),
                "same-location reference lost its nested symbolic field "
                        + "through a getter: " + nested);
        DataKeyShape shaped = new DataKeyShape(sameLocationRef.getValue(),
                "pool", new byte[] { 1 }, new byte[] { 2 }, 9L, "alg");
        String shapedKeyId = System.getSymbolicFieldExpression(
                shaped, DataKeyShape.class.getName(), "keyId", "I",
                Integer.valueOf(shaped.keyId));
        require(shapedKeyId.contains(NESTED_SOURCE),
                "multi-argument constructor lost its leading symbolic int: "
                        + shapedKeyId);
        assertExactDestinationEvidence(producer, "currentKey", refDesc(),
                refVersion, SAME_LOCATION_EDGE);

        // Every refusal happens before a destination shadow or evidence alias
        // is installed.  The pure destination envelope therefore stays byte
        // for byte unchanged.
        Consumer wrongValue = new Consumer();
        wrongValue.needKeyUpdate = false;
        assertRefusedWithoutState(wrongValue, "needKeyUpdate", "Z",
                boolVersion, BOOL_EDGE);

        Consumer unknownVersion = new Consumer();
        unknownVersion.needKeyUpdate = true;
        assertRefusedWithoutState(unknownVersion, "needKeyUpdate", "Z",
                Long.MAX_VALUE, BOOL_EDGE);

        Consumer missingEdge = new Consumer();
        missingEdge.needKeyUpdate = true;
        assertRefusedWithoutState(missingEdge, "needKeyUpdate", "Z",
                boolVersion, "");

        ObjectConsumer wrongDescriptor = new ObjectConsumer();
        wrongDescriptor.currentKey = new Ref(7);
        String wrongBefore = System.getSharedFieldVersions(
                wrongDescriptor, ObjectConsumer.class.getName(),
                "currentKey", "Ljava/lang/Object;");
        require(System.admitSharedFieldVersion(
                wrongDescriptor, ObjectConsumer.class.getName(),
                "currentKey", "Ljava/lang/Object;", refVersion, REF_EDGE)
                < 0L, "mismatched reference descriptor was admitted");
        require(wrongBefore.equals(System.getSharedFieldVersions(
                wrongDescriptor, ObjectConsumer.class.getName(),
                "currentKey", "Ljava/lang/Object;")),
                "descriptor refusal allocated state or alias");

        Consumer wrongNullness = new Consumer();
        wrongNullness.nullableKey = new Ref(9);
        assertRefusedWithoutState(wrongNullness, "nullableKey", refDesc(),
                nullVersion, NULL_EDGE);

        Consumer consumer = new Consumer();
        consumer.needKeyUpdate = true;
        // A deserialized reference may be a distinct concrete object. Exact
        // descriptor and nullness are the reference replay contract.
        consumer.currentKey = new Ref(7);
        consumer.nullableKey = null;

        String boolBefore = versions(consumer, "needKeyUpdate", "Z");
        require(boolBefore.contains("\"selected\":false"), boolBefore);
        require(System.admitSharedFieldVersion(
                consumer, Consumer.class.getName(), "needKeyUpdate", "Z",
                boolVersion, BOOL_EDGE) == boolVersion,
                "boolean exact version rejected");
        boolean observedBool = consumer.needKeyUpdate;
        require(observedBool, "concrete boolean replay diverged");
        assertExactDestinationEvidence(consumer, "needKeyUpdate", "Z",
                boolVersion, BOOL_EDGE);
        String oneShotBefore = versions(consumer, "needKeyUpdate", "Z");
        require(consumer.needKeyUpdate,
                "second concrete boolean read diverged");
        String oneShotAfter = versions(consumer, "needKeyUpdate", "Z");
        require(oneShotBefore.equals(oneShotAfter),
                "one planned admission recorded more than one read: "
                        + oneShotAfter);

        require(System.admitSharedFieldVersion(
                consumer, Consumer.class.getName(), "currentKey", refDesc(),
                refVersion, REF_EDGE) == refVersion,
                "reference exact version rejected");
        Ref observedRef = consumer.currentKey;
        require(observedRef != null && observedRef.value == 7,
                "concrete reference replay diverged");
        assertExactDestinationEvidence(consumer, "currentKey", refDesc(),
                refVersion, REF_EDGE);

        require(System.admitSharedFieldVersion(
                consumer, Consumer.class.getName(), "nullableKey", refDesc(),
                nullVersion, NULL_EDGE) == nullVersion,
                "null exact version rejected");
        Ref observedNull = consumer.nullableKey;
        require(observedNull == null, "concrete null replay diverged");
        assertExactDestinationEvidence(consumer, "nullableKey", refDesc(),
                nullVersion, NULL_EDGE);

        // A store between admission and the planned load invalidates both the
        // pending read and its destination evidence alias. The following real
        // getfield must remain an ordinary concrete read with no ledger edge.
        Consumer overwritten = new Consumer();
        overwritten.needKeyUpdate = true;
        require(System.admitSharedFieldVersion(
                overwritten, Consumer.class.getName(), "needKeyUpdate", "Z",
                boolVersion, CANCEL_EDGE) == boolVersion,
                "pre-write cancellation setup was rejected");
        String ledgerBeforeCancel = System.getEventLedger();
        overwritten.needKeyUpdate = false;
        require(!overwritten.needKeyUpdate,
                "concrete overwrite did not reach the real field");
        String overwrittenEvidence = versions(
                overwritten, "needKeyUpdate", "Z");
        require(overwrittenEvidence.contains("\"selected\":false"),
                "pre-read write retained producer alias: "
                        + overwrittenEvidence);
        require(!overwrittenEvidence.contains(CANCEL_EDGE),
                overwrittenEvidence);
        require(ledgerBeforeCancel.equals(System.getEventLedger()),
                "cancelled pending read emitted a ledger edge");

        String ledger = System.getEventLedger();
        require(count(ledger, "\"edgeKind\":\"FIELD_READ_FROM\"") >= 3,
                ledger);
        require(ledger.contains("\"beforeEventId\":" + boolVersion),
                ledger);
        require(ledger.contains("\"beforeEventId\":" + refVersion),
                ledger);
        require(ledger.contains("\"beforeEventId\":" + nullVersion),
                ledger);

        require(System.finishConcolicRegion().contains("\"complete\":true"),
                "consumer summary incomplete");
        require(System.closeWorkloadSession() == 0L,
                "workload session did not close");
        System.out.println("CAUSYNTH_SHARED_FIELD_PRODUCER_STATE_SMOKE_OK");
    }

    private static long pureCurrentVersion(
            Producer owner, String field, String descriptor) {
        String before = versions(owner, field, descriptor);
        long version = System.getCurrentSharedFieldVersion(
                owner, Producer.class.getName(), field, descriptor);
        require(version > 0L, "current producer version missing: " + version);
        String after = versions(owner, field, descriptor);
        require(before.equals(after),
                "current-version query mutated evidence: " + after);
        return version;
    }

    private static void assertRefusedWithoutState(
            Consumer owner, String field, String descriptor, long version,
            String edge) {
        String before = versions(owner, field, descriptor);
        require(System.admitSharedFieldVersion(
                owner, Consumer.class.getName(), field, descriptor,
                version, edge) < 0L, "invalid admission unexpectedly succeeded");
        String after = versions(owner, field, descriptor);
        require(before.equals(after),
                "refusal allocated destination state or alias: " + after);
        require(after.contains("\"selected\":false"), after);
    }

    private static void assertExactDestinationEvidence(
            Object owner, String field, String descriptor, long version,
            String edge) {
        String evidence = versions(owner, field, descriptor);
        require(evidence.contains("\"resolution\":\"EXACT\""), evidence);
        require(evidence.contains(
                "\"reason\":\"PLANNED_PRODUCER_STATE\""), evidence);
        require(evidence.contains("\"selectedEdgeId\":\"" + edge + "\""),
                evidence);
        require(evidence.contains(
                "\"chosenFieldVersionId\":" + version), evidence);
        // The producer version belongs to another task.  Whether this owner
        // is an evidence alias or the source location itself, a pure query in
        // the consumer task may not republish it as a consumer version.
        require(System.getCurrentSharedFieldVersion(
                owner, owner.getClass().getName(), field, descriptor) < 0L,
                "admission minted a destination carrier/INITIAL");
    }

    private static String versions(
            Object owner, String field, String descriptor) {
        return System.getSharedFieldVersions(
                owner, owner.getClass().getName(), field, descriptor);
    }

    private static String refDesc() {
        return "LRegionSharedFieldProducerStateSmoke$Ref;";
    }

    private static int count(String text, String needle) {
        int total = 0;
        int index = 0;
        while ((index = text.indexOf(needle, index)) >= 0) {
            total++;
            index += needle.length();
        }
        return total;
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
