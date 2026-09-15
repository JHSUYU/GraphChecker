import java.util.LinkedHashMap;
import java.util.Map;

/** Focused smoke test for the sole RPC symbolic propagation authority. */
public final class RegionExpressionHandoffApiSmoke {
    private static final class Sender {
        int keyId = 7;
    }

    private static final class Receiver {
        int keyId;
    }

    private static final class ContainerSender {
        Object[] values = new Object[]{"a", "b"};
    }

    private static final class ContainerReceiver {
        Object[] values = new Object[]{"a", "b"};
    }

    private static final class Element {
        final int keyId;

        private Element(int keyId) {
            this.keyId = keyId;
        }
    }

    private static final class ElementArraySender {
        Element[] values;

        private ElementArraySender(Element[] values) {
            this.values = values;
        }
    }

    private static final class ElementArrayReceiver {
        Element[] values;

        private ElementArrayReceiver(Element[] values) {
            this.values = values;
        }
    }

    public static void main(String[] args) {
        require(System.startConcolicRegion("REGION.handoff",
                "TASK.handoff") == 0L, "region start rejected");

        symbolicPrimitiveKeepsNestedConsumerBoundaries();
        oneExportReachesSeveralReceivers();
        concretePrimitiveKeepsItsHandoffLineage();
        indexedContainerKeepsItsState();
        indexedContainerCarriesElementFieldsIntoMap();

        require(System.finishConcolicRegion().contains("\"complete\":true"),
                "region finish failed");
        System.out.println("RegionExpressionHandoffApiSmoke OK");
    }

    /** A forwarded value keeps both consumer boundaries around one payload. */
    private static void symbolicPrimitiveKeepsNestedConsumerBoundaries() {
        Sender sender = new Sender();
        System.symbolizeExactField(sender, Sender.class.getName(), "keyId",
                "I", "RPC.keyId");
        long[] exported = new long[1];
        long handle = System.exportExpression(sender,
                Sender.class.getName(), "keyId", "I", exported);
        require(handle > 0L, "export rejected: " + handle);
        require(exported[0] > 0L, "export named no endpoint event");

        Receiver receiver = new Receiver();
        receiver.keyId = sender.keyId;
        long[] attached = new long[1];
        long exportEvent = System.attachExpression(receiver,
                Receiver.class.getName(), "keyId", "I", handle, attached);
        require(exportEvent == exported[0], "attach rejected: " + exportEvent);
        require(attached[0] > 0L, "attach named no endpoint event");

        long[] forwarded = new long[1];
        long forwardedHandle = System.exportExpression(receiver,
                Receiver.class.getName(), "keyId", "I", forwarded);
        require(forwardedHandle > 0L,
                "forwarded export rejected: " + forwardedHandle);

        Receiver downstream = new Receiver();
        downstream.keyId = receiver.keyId;
        long[] downstreamAttach = new long[1];
        long forwardedEvent = System.attachExpression(downstream,
                Receiver.class.getName(), "keyId", "I", forwardedHandle,
                downstreamAttach);
        require(forwardedEvent == forwarded[0],
                "forwarded attach rejected: " + forwardedEvent);
        require(downstreamAttach[0] > 0L,
                "forwarded attach named no endpoint event");

        // The wrapper is an identity in the VM expression algebra: ordinary
        // receiver computation must build on the nested payload rather than
        // replacing it with a fresh input or treating the boundary as an op.
        downstream.keyId = downstream.keyId + 1;
        require(downstream.keyId == sender.keyId + 1,
                "consumer boundary changed the concrete value");

        String expression = System.getSymbolicFieldExpression(downstream,
                Receiver.class.getName(), "keyId", "I",
                Integer.valueOf(downstream.keyId));
        require(expression.contains("RPC.keyId"), expression);
        // One RPC_ATTACH boundary per hop, both retained around one payload.
        require(count(expression, "\"boundaryKind\":\"RPC_ATTACH\"") == 2,
                "two-hop expression did not retain two attach boundaries: "
                        + expression);
        require(expression.contains("\"eventId\":" + attached[0]),
                "first consumer event is absent: " + expression);
        require(expression.contains("\"eventId\":" + downstreamAttach[0]),
                "second consumer event is absent: " + expression);
        // The attach reaches the read.  An attach publishes a version on the
        // destination, so the getfield that follows resolves over the log --
        // exactly one FIELD_READ wrapper, over the WRITE version the attach
        // published.  Before the attach published, this destination's log had
        // already been started by `downstream.keyId = receiver.keyId` and the
        // read took the ordinary write instead: three FIELD_READ boundaries,
        // no RPC_ATTACH, and the RPC lineage cut at the attach hop.
        require(count(expression, "\"boundaryKind\":\"FIELD_READ\"") == 1,
                "the read did not resolve to the attach: " + expression);
        require(expression.contains("\"_type\":\"ReadFromExpression\""),
                expression);
        require(expression.contains("\"versionKind\":\"WRITE\""), expression);
    }

    /**
     * One exported expression, several explicit receivers.
     *
     * <p>Each attach reports its own endpoint event. The export id alone cannot
     * name a receive because several receivers may attach the same payload.</p>
     */
    private static void oneExportReachesSeveralReceivers() {
        Sender sender = new Sender();
        System.symbolizeExactField(sender, Sender.class.getName(), "keyId",
                "I", "RPC.fanout");
        long[] exported = new long[1];
        long handle = System.exportExpression(sender,
                Sender.class.getName(), "keyId", "I", exported);
        require(handle > 0L, "fan-out export rejected: " + handle);

        Receiver first = new Receiver();
        long[] firstAttach = new long[1];
        require(System.attachExpression(first, Receiver.class.getName(),
                "keyId", "I", handle, firstAttach) == exported[0],
                "first attach rejected");

        Receiver second = new Receiver();
        long[] secondAttach = new long[1];
        require(System.attachExpression(second, Receiver.class.getName(),
                "keyId", "I", handle, secondAttach) == exported[0],
                "second attach rejected");

        require(firstAttach[0] != secondAttach[0],
                "two receivers reported one attach event");
    }

    private static void concretePrimitiveKeepsItsHandoffLineage() {
        Sender sender = new Sender();
        long[] exported = new long[1];
        long handle = System.exportExpression(sender,
                Sender.class.getName(), "keyId", "I", exported);
        require(handle > 0L, "concrete export rejected: " + handle);

        Receiver receiver = new Receiver();
        receiver.keyId = sender.keyId;
        long[] attached = new long[1];
        long exportEvent = System.attachExpression(receiver,
                Receiver.class.getName(), "keyId", "I", handle, attached);
        require(exportEvent == exported[0],
                "concrete attach rejected: " + exportEvent);
        require(attached[0] > 0L, "concrete attach named no endpoint event");

        String expression = System.getSymbolicFieldExpression(receiver,
                Receiver.class.getName(), "keyId", "I",
                Integer.valueOf(receiver.keyId));
        require(expression.contains("ConstExpr"), expression);
        require(expression.contains("Y_I_7"), expression);
    }

    private static void indexedContainerKeepsItsState() {
        ContainerSender sender = new ContainerSender();
        require(System.trackContainerExpression(sender.values,
                "RPC.values"), "array state was not tracked");
        long[] exported = new long[1];
        long handle = System.exportExpression(sender,
                ContainerSender.class.getName(), "values",
                "[Ljava/lang/Object;", exported);
        require(handle > 0L, "container export rejected: " + handle);

        ContainerReceiver receiver = new ContainerReceiver();
        long[] attached = new long[1];
        long exportEvent = System.attachExpression(receiver,
                ContainerReceiver.class.getName(), "values",
                "[Ljava/lang/Object;", handle, attached);
        require(exportEvent == exported[0], "container attach rejected: "
                + exportEvent);
        String expression = System.getSymbolicExpression(receiver.values);
        require(expression.contains("RPC.values"), expression);

        ContainerReceiver wrongLength = new ContainerReceiver();
        wrongLength.values = new Object[]{"a"};
        long[] refused = new long[1];
        require(System.attachExpression(wrongLength,
                ContainerReceiver.class.getName(), "values",
                "[Ljava/lang/Object;", handle, refused) < 0L,
                "mismatched fixed array length was accepted");
        require(refused[0] == 0L, "a refused attach named an endpoint event");
    }

    private static void indexedContainerCarriesElementFieldsIntoMap() {
        Map<Integer, Element> source =
                new LinkedHashMap<Integer, Element>();
        source.put(Integer.valueOf(7), new Element(7));
        source.put(Integer.valueOf(11), new Element(11));
        require(System.trackContainerExpression(source,
                "RPC.allKeys"), "source map state was not tracked");

        ElementArraySender sender = new ElementArraySender(
                source.values().toArray(new Element[0]));
        long[] exported = new long[1];
        long handle = System.exportExpression(sender,
                ElementArraySender.class.getName(), "values",
                "[LRegionExpressionHandoffApiSmoke$Element;", exported);
        require(handle > 0L, "element array export rejected: " + handle);

        ElementArrayReceiver receiver = new ElementArrayReceiver(
                new Element[]{new Element(7), new Element(11)});
        long[] attached = new long[1];
        long exportEvent = System.attachExpression(receiver,
                ElementArrayReceiver.class.getName(), "values",
                "[LRegionExpressionHandoffApiSmoke$Element;", handle,
                attached);
        require(exportEvent == exported[0],
                "element array attach rejected: " + exportEvent);
        require(attached[0] > 0L,
                "element array attach named no endpoint event");

        Map<Integer, Element> rebuilt =
                new LinkedHashMap<Integer, Element>();
        for (int index = 0; index < receiver.values.length; index++) {
            Element element = receiver.values[index];
            rebuilt.put(Integer.valueOf(element.keyId), element);
        }
        String expression = System.getSymbolicExpression(rebuilt);
        require(expression.contains("\"operation\":\"PUT\""), expression);
        require(expression.contains("\"operation\":\"READ\""), expression);
        require(expression.contains("\"operation\":\"WRITE\""), expression);
        require(expression.contains("\"operation\":\"NEXT\""), expression);
        require(expression.contains("VALUE_VIEW"), expression);
        require(expression.contains("RPC.allKeys"), expression);
        require(expression.contains("_field"), expression);
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }

    private static int count(String value, String needle) {
        int found = 0;
        int offset = 0;
        while ((offset = value.indexOf(needle, offset)) >= 0) {
            found++;
            offset += needle.length();
        }
        return found;
    }
}
