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

        symbolicPrimitiveKeepsItsExpression();
        oneExportReachesSeveralReceivers();
        concretePrimitiveKeepsItsHandoffLineage();
        indexedContainerKeepsItsState();
        indexedContainerCarriesElementFieldsIntoMap();

        require(System.finishConcolicRegion().contains("\"complete\":true"),
                "region finish failed");
    }

    private static void symbolicPrimitiveKeepsItsExpression() {
        Sender sender = new Sender();
        System.symbolizeExactField(sender, Sender.class.getName(), "keyId",
                "I", "RPC.keyId");
        long[] exported = new long[1];
        long handle = System.exportExpression(sender,
                Sender.class.getName(), "keyId", "I", exported);
        require(handle > 0L, "export rejected: " + handle);
        require(exported[0] > 0L, "export named no ledger event");

        Receiver receiver = new Receiver();
        receiver.keyId = sender.keyId;
        long[] attached = new long[1];
        long exportEvent = System.attachExpression(receiver,
                Receiver.class.getName(), "keyId", "I", handle, attached);
        require(exportEvent == exported[0], "attach rejected: " + exportEvent);
        require(attached[0] > 0L, "attach named no ledger event");

        String expression = System.getSymbolicFieldExpression(receiver,
                Receiver.class.getName(), "keyId", "I",
                Integer.valueOf(receiver.keyId));
        require(expression.contains("RPC.keyId"), expression);
        String ledger = System.getEventLedger();
        require(ledger.contains(edge(exportEvent, attached[0])), ledger);
    }

    /**
     * One exported expression, several explicit receivers.
     *
     * <p>Each attach records its own {@code VALUE_HANDOFF} edge and reports
     * its own attach event, and nothing is tallied.  This is why the export
     * id alone cannot name a receive: both edges leave the same export, so a
     * consumer that picked one of them would be naming a receiver it did not
     * mean.  README {@code RPC-1}.</p>
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
        String ledger = System.getEventLedger();
        require(ledger.contains(edge(exported[0], firstAttach[0])), ledger);
        require(ledger.contains(edge(exported[0], secondAttach[0])), ledger);
    }

    /** The exact serialized VALUE_HANDOFF edge joining one endpoint pair. */
    private static String edge(long exportEvent, long attachEvent) {
        return "{\"beforeEventId\":" + exportEvent
                + ",\"afterEventId\":" + attachEvent
                + ",\"edgeKind\":\"VALUE_HANDOFF\"}";
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
        require(attached[0] > 0L, "concrete attach named no ledger event");

        String expression = System.getSymbolicFieldExpression(receiver,
                Receiver.class.getName(), "keyId", "I",
                Integer.valueOf(receiver.keyId));
        require(expression.contains("ConstExpr"), expression);
        require(expression.contains("Y_I_7"), expression);
        String ledger = System.getEventLedger();
        require(ledger.contains(edge(exportEvent, attached[0])), ledger);
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
        require(System.getEventLedger().contains(
                edge(exportEvent, attached[0])), System.getEventLedger());

        ContainerReceiver wrongLength = new ContainerReceiver();
        wrongLength.values = new Object[]{"a"};
        long[] refused = new long[1];
        require(System.attachExpression(wrongLength,
                ContainerReceiver.class.getName(), "values",
                "[Ljava/lang/Object;", handle, refused) < 0L,
                "mismatched fixed array length was accepted");
        // A refused attach records no event, so it reports none either.
        require(refused[0] == 0L, "a refused attach named a ledger event");
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
                "element array attach named no ledger event");

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
}
