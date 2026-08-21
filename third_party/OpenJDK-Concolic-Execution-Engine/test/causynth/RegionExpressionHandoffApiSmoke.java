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
        long handle = System.exportExpression(sender,
                Sender.class.getName(), "keyId", "I");
        require(handle > 0L, "export rejected: " + handle);

        Receiver receiver = new Receiver();
        receiver.keyId = sender.keyId;
        long exportEvent = System.attachExpression(receiver,
                Receiver.class.getName(), "keyId", "I", handle);
        require(exportEvent > 0L, "attach rejected: " + exportEvent);

        String expression = System.getSymbolicFieldExpression(receiver,
                Receiver.class.getName(), "keyId", "I",
                Integer.valueOf(receiver.keyId));
        require(expression.contains("RPC.keyId"), expression);
        String ledger = System.getEventLedger();
        require(ledger.contains("VALUE_HANDOFF"), ledger);
        require(ledger.contains(String.valueOf(exportEvent)), ledger);
    }

    private static void concretePrimitiveKeepsItsHandoffLineage() {
        Sender sender = new Sender();
        long handle = System.exportExpression(sender,
                Sender.class.getName(), "keyId", "I");
        require(handle > 0L, "concrete export rejected: " + handle);

        Receiver receiver = new Receiver();
        receiver.keyId = sender.keyId;
        long exportEvent = System.attachExpression(receiver,
                Receiver.class.getName(), "keyId", "I", handle);
        require(exportEvent > 0L, "concrete attach rejected: " + exportEvent);

        String expression = System.getSymbolicFieldExpression(receiver,
                Receiver.class.getName(), "keyId", "I",
                Integer.valueOf(receiver.keyId));
        require(expression.contains("ConstExpr"), expression);
        require(expression.contains("Y_I_7"), expression);
        String ledger = System.getEventLedger();
        require(ledger.contains("VALUE_HANDOFF"), ledger);
        require(ledger.contains(String.valueOf(exportEvent)), ledger);
    }

    private static void indexedContainerKeepsItsState() {
        ContainerSender sender = new ContainerSender();
        require(System.trackContainerExpression(sender.values,
                "RPC.values"), "array state was not tracked");
        long handle = System.exportExpression(sender,
                ContainerSender.class.getName(), "values",
                "[Ljava/lang/Object;");
        require(handle > 0L, "container export rejected: " + handle);

        ContainerReceiver receiver = new ContainerReceiver();
        long exportEvent = System.attachExpression(receiver,
                ContainerReceiver.class.getName(), "values",
                "[Ljava/lang/Object;", handle);
        require(exportEvent > 0L, "container attach rejected: "
                + exportEvent);
        String expression = System.getSymbolicExpression(receiver.values);
        require(expression.contains("RPC.values"), expression);
        require(System.getEventLedger().contains("VALUE_HANDOFF"),
                System.getEventLedger());

        ContainerReceiver wrongLength = new ContainerReceiver();
        wrongLength.values = new Object[]{"a"};
        require(System.attachExpression(wrongLength,
                ContainerReceiver.class.getName(), "values",
                "[Ljava/lang/Object;", handle) < 0L,
                "mismatched fixed array length was accepted");
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
        long handle = System.exportExpression(sender,
                ElementArraySender.class.getName(), "values",
                "[LRegionExpressionHandoffApiSmoke$Element;");
        require(handle > 0L, "element array export rejected: " + handle);

        ElementArrayReceiver receiver = new ElementArrayReceiver(
                new Element[]{new Element(7), new Element(11)});
        long exportEvent = System.attachExpression(receiver,
                ElementArrayReceiver.class.getName(), "values",
                "[LRegionExpressionHandoffApiSmoke$Element;", handle);
        require(exportEvent > 0L,
                "element array attach rejected: " + exportEvent);

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
