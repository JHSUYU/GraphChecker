import java.util.ArrayDeque;
import java.util.LinkedHashSet;
import java.util.Queue;
import java.util.Set;

public final class RegionBoxedPrimitiveApiSmoke {
    private static void requirePrimitive(Object value, String descriptor) {
        String expression = System.getSymbolicExpression(value);
        require(expression.contains("\"symbolic\":true")
                        && expression.contains("\"javaTypeDescriptor\":\""
                        + descriptor + "\"")
                        && expression.contains("\"_java_type\":\""
                        + descriptor + "\"")
                        && !expression.contains("\"_java_type\":\"L\""),
                descriptor + " wrapper lost its primitive shadow: "
                        + expression);
    }

    public static void main(String[] args) {
        long status = System.startConcolicRegion(
                "REGION.BOXED.PRIMITIVE", "ACT.BOXED.PRIMITIVE");
        require(status == 0L, "region start rejected");

        Boolean bool = new Boolean(true);
        Byte bite = new Byte((byte) 7);
        Short shortValue = new Short((short) 8);
        Character character = new Character('A');
        Integer integer = new Integer(9);
        Long longValue = new Long(10L);
        Float floatValue = new Float(11.5F);
        Double doubleValue = new Double(12.5D);

        System.symbolize(bool, "boxed_boolean");
        System.symbolize(bite, "boxed_byte");
        System.symbolize(shortValue, "boxed_short");
        System.symbolize(character, "boxed_character");
        System.symbolize(integer, "boxed_integer");
        System.symbolize(longValue, "boxed_long");
        System.symbolize(floatValue, "boxed_float");
        System.symbolize(doubleValue, "boxed_double");

        requirePrimitive(new Boolean(bool.booleanValue()), "Z");
        requirePrimitive(new Byte(bite.byteValue()), "B");
        requirePrimitive(new Short(shortValue.shortValue()), "S");
        requirePrimitive(new Character(character.charValue()), "C");
        requirePrimitive(new Integer(integer.intValue()), "I");
        requirePrimitive(new Long(longValue.longValue()), "J");
        requirePrimitive(new Float(floatValue.floatValue()), "F");
        requirePrimitive(new Double(doubleValue.doubleValue()), "D");

        Set<Integer> set = new LinkedHashSet<>();
        set.add(new Integer(13));
        Integer selected = set.iterator().next();
        System.symbolize(selected, "boxed_set_next");
        requirePrimitive(new Integer(selected.intValue()), "I");

        Queue<Integer> queue = new ArrayDeque<>();
        queue.add(new Integer(14));
        Integer polled = queue.poll();
        System.symbolize(polled, "boxed_queue_poll");
        requirePrimitive(new Integer(polled.intValue()), "I");

        String summary = System.finishConcolicRegion();
        require(summary.contains("\"complete\":true"), summary);
        System.out.println("RegionBoxedPrimitiveApiSmoke passed");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
