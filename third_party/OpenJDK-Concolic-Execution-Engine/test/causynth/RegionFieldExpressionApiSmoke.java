/** Exact normal-exit field shadow and concrete-value observations. */
public final class RegionFieldExpressionApiSmoke {
    private static final class Holder {
        String text = "seed";
        int count = 7;
        Object nullable = new Object();

        int getCount() {
            return count;
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
        require(concreteInt.contains("\"kind\":\"CONCRETE_PRIMITIVE\""),
                concreteInt);

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
        require(concreteElementInt.contains(
                "\"kind\":\"CONCRETE_PRIMITIVE\""),
                concreteElementInt);
        require(concreteElementInt.contains("\"_exp\":\"Y_I_42\""),
                concreteElementInt);

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
