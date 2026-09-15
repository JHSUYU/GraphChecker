/** Exact normal-exit field shadow and concrete-value observations. */
public final class RegionFieldExpressionApiSmoke {
    private static volatile int sink;

    private static final class Holder {
        String text = "seed";
        int count = 7;
        boolean selected = true;
        boolean observed;
        Object nullable = new Object();

        int getCount() {
            return count;
        }

        synchronized boolean isSelected() {
            return selected;
        }
    }

    private static class Base {
        int value = 11;
    }

    private static final class Derived extends Base {
        int value = 22;
    }

    public static void main(String[] args) {
        long status = System.startConcolicRegion(
                "REGION.field-expression", "TASK.field-expression");
        require(status == 0L, "region start rejected");

        Holder holder = new Holder();
        System.symbolizeField(holder, "text", "FIELD.text");
        String frame = System.getSymbolicFieldExpression(
                holder, Holder.class.getName(), "text",
                "Ljava/lang/String;", holder.text);
        require(frame.contains("\"kind\":\"SYMBOLIC_FIELD\""), frame);

        holder.text = "literal";
        String literal = System.getSymbolicFieldExpression(
                holder, Holder.class.getName(), "text",
                "Ljava/lang/String;", holder.text);
        require(literal.contains("\"kind\":\"CONCRETE_STRING\""), literal);
        require(literal.contains("\"_type\":\"ConStringSymbolExp\""),
                literal);

        System.symbolizeField(holder, "count", "FIELD.count");
        holder.count = 42;
        String concreteInt = System.getSymbolicFieldExpression(
                holder, Holder.class.getName(), "count", "I",
                Integer.valueOf(holder.count));
        // The mint started this location's log, so the concrete store that
        // followed is a WRITE version on it, and the read of the field
        // resolves over the log rather than over the owner shadow: a guarded
        // read whose observed version wrote Y_I_42.  The minted symbol is
        // gone because the store overwrote it -- that is the whole content of
        // "a concrete store into a tracked location is kept".  The envelope
        // describes the boxed operand this read produced, the field itself
        // having no shadow left after the concrete store.
        require(concreteInt.contains("\"kind\":\"SYMBOLIC_OBJECT\""),
                concreteInt);
        require(concreteInt.contains("\"boundaryKind\":\"FIELD_READ\""),
                concreteInt);
        require(concreteInt.contains("\"_type\":\"ReadFromExpression\""),
                concreteInt);
        require(concreteInt.contains("\"locationKind\":\"INSTANCE_FIELD\""),
                concreteInt);
        require(concreteInt.contains("\"versionKind\":\"WRITE\""),
                concreteInt);
        require(concreteInt.contains("\"_exp\":\"Y_I_42\""), concreteInt);
        require(!concreteInt.contains("FIELD.count"), concreteInt);

        Holder[] holders = new Holder[]{new Holder(), new Holder()};
        require(System.trackContainerExpression(holders, "FIELD.holders"),
                "array tracking rejected");
        Holder element = holders[1];
        System.symbolizeExactField(
                element, Holder.class.getName(), "count", "I",
                "FIELD.element.count");
        element.count = 42;
        int observedCount = holders[1].getCount();
        String concreteElementInt = System.getSymbolicFieldExpression(
                holders[1], Holder.class.getName(), "count", "I",
                Integer.valueOf(observedCount));
        // Same rule on an element's own field: the exact mint started the
        // log, the concrete store is a WRITE version on it, and the getter's
        // read resolves over the log to that version's value.
        require(concreteElementInt.contains("\"kind\":\"SYMBOLIC_OBJECT\""),
                concreteElementInt);
        require(concreteElementInt.contains(
                "\"_type\":\"ReadFromExpression\""), concreteElementInt);
        require(concreteElementInt.contains("\"versionKind\":\"WRITE\""),
                concreteElementInt);
        require(concreteElementInt.contains("\"_exp\":\"Y_I_42\""),
                concreteElementInt);
        require(!concreteElementInt.contains("FIELD.element.count"),
                concreteElementInt);

        System.symbolizeExactField(
                holder, Holder.class.getName(), "selected", "Z",
                "FIELD.selected");
        holder.observed = holder.isSelected();
        if (holder.observed) sink++;
        String getterReturn = System.getSymbolicFieldExpression(
                holder, Holder.class.getName(), "observed", "Z",
                Boolean.valueOf(holder.observed));
        require(getterReturn.contains("FIELD.selected"), getterReturn);

        System.symbolizeField(holder, "nullable", "FIELD.nullable");
        holder.nullable = null;
        String nullReference = System.getSymbolicFieldExpression(
                holder, Holder.class.getName(), "nullable",
                "Ljava/lang/Object;", holder.nullable);
        require(nullReference.contains("\"kind\":\"NULL_REFERENCE\""),
                nullReference);
        require(!nullReference.contains("\"expression\":null"),
                nullReference);

        Derived hidden = new Derived();
        System.symbolizeExactField(
                hidden, Base.class.getName(), "value", "I",
                "FIELD.base.value");
        System.symbolizeExactField(
                hidden, Derived.class.getName(), "value", "I",
                "FIELD.derived.value");
        String baseValue = System.getSymbolicFieldExpression(
                hidden, Base.class.getName(), "value", "I",
                Integer.valueOf(((Base) hidden).value));
        String derivedValue = System.getSymbolicFieldExpression(
                hidden, Derived.class.getName(), "value", "I",
                Integer.valueOf(hidden.value));
        require(baseValue.contains("FIELD.base.value"), baseValue);
        require(!baseValue.contains("FIELD.derived.value"), baseValue);
        require(derivedValue.contains("FIELD.derived.value"), derivedValue);
        require(!derivedValue.contains("FIELD.base.value"), derivedValue);

        String summary = System.finishConcolicRegion();
        require(summary.contains("\"complete\":true"), summary);
        System.out.println("CAUSYNTH_REGION_FIELD_EXPRESSION_API_SMOKE_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
