/**
 * Verifies that primitive string conversion provenance is signature-aware and
 * that the Java 8 append-only StringBuilder lowering retains its expression.
 */
public final class RegionStringConversionApiSmoke {
    public static void main(String[] args) {
        Integer integer = Integer.valueOf(42);
        Long longValue = Long.valueOf(42L);
        Boolean booleanValue = Boolean.TRUE;

        System.startConcolicRegion("REGION.string-conversion",
                "ACT.string-conversion");
        System.symbolize(integer, "string_conversion_integer");
        System.symbolize(longValue, "string_conversion_long");
        System.symbolize(booleanValue, "string_conversion_boolean");

        String decimalStatic = Integer.toString(integer.intValue());
        String decimalInstance = integer.toString();
        String radix = Integer.toString(integer.intValue(), 16);
        String hexadecimal = Integer.toHexString(integer.intValue());
        String longStatic = Long.toString(longValue.longValue());
        String longInstance = longValue.toString();
        // Both calls return an interned String.  The VM cannot attach a
        // per-execution symbolic identity to that shared object, so it must
        // retain explicit unsupported provenance in the region summary.
        String booleanStatic = Boolean.toString(booleanValue.booleanValue());
        String booleanInstance = booleanValue.toString();

        StringBuilder builder = new StringBuilder();
        builder.append("key=").append(integer.intValue());
        String builderBeforeToString = System.getSymbolicExpression(builder);
        String builderValue = builder.toString();

        String decimalStaticExpression =
                System.getSymbolicExpression(decimalStatic);
        String decimalInstanceExpression =
                System.getSymbolicExpression(decimalInstance);
        String radixExpression = System.getSymbolicExpression(radix);
        String hexadecimalExpression =
                System.getSymbolicExpression(hexadecimal);
        String longStaticExpression =
                System.getSymbolicExpression(longStatic);
        String longInstanceExpression =
                System.getSymbolicExpression(longInstance);
        String builderValueExpression =
                System.getSymbolicExpression(builderValue);
        String summary = System.finishConcolicRegion();

        require(decimalStaticExpression.contains("\"_name\":\"toString\""),
                decimalStaticExpression);
        require(decimalInstanceExpression.contains("\"_name\":\"toString\""),
                decimalInstanceExpression);
        require(!decimalStaticExpression.contains(
                "unsupportedPrimitiveStringConversion"),
                decimalStaticExpression);
        require(!decimalInstanceExpression.contains(
                "unsupportedPrimitiveStringConversion"),
                decimalInstanceExpression);

        String radixOperation = "unsupportedPrimitiveStringConversion:"
                + "java/lang/Integer.toString(II)Ljava/lang/String;";
        require(radixExpression.contains(radixOperation), radixExpression);
        require(radixExpression.contains("\"_exp\":\"Y_I_16\""),
                radixExpression);

        String hexOperation = "unsupportedPrimitiveStringConversion:"
                + "java/lang/Integer.toHexString(I)Ljava/lang/String;";
        require(hexadecimalExpression.contains(hexOperation),
                hexadecimalExpression);
        require(!hexadecimalExpression.contains(radixOperation),
                hexadecimalExpression);

        require(longStaticExpression.contains(
                "unsupportedPrimitiveStringConversion:"
                        + "java/lang/Long.toString(J)Ljava/lang/String;"),
                longStaticExpression);
        require(longInstanceExpression.contains(
                "unsupportedPrimitiveStringConversion:"
                        + "java/lang/Long.toString()Ljava/lang/String;"),
                longInstanceExpression);

        require(builderBeforeToString.contains("\"symbolic\":true"),
                builderBeforeToString);
        require(builderBeforeToString.contains("\"_name\":\"concat\""),
                builderBeforeToString);
        require(builderValueExpression.contains("\"symbolic\":true"),
                builderValueExpression);
        require(builderValueExpression.contains("\"_name\":\"concat\""),
                builderValueExpression);
        require(builderValueExpression.contains("\"_name\":\"toString\""),
                builderValueExpression);
        // getSymbolicExpression is observational and must not add an otherwise
        // unused value to the path condition.
        require(summary.contains("\"regionId\":\"REGION.string-conversion\""),
                summary);
        require(summary.contains(
                "\"activationId\":\"ACT.string-conversion\""), summary);
        require(summary.contains(
                "unsupportedPrimitiveStringConversion:"
                        + "java/lang/Boolean.toString(Z)Ljava/lang/String;"),
                summary);
        require(summary.contains(
                "unsupportedPrimitiveStringConversion:"
                        + "java/lang/Boolean.toString()Ljava/lang/String;"),
                summary);
        require(summary.contains("string_conversion_boolean"), summary);
        require("true".equals(booleanStatic), booleanStatic);
        require("true".equals(booleanInstance), booleanInstance);
        System.out.println("CAUSYNTH_REGION_STRING_CONVERSION_API_SMOKE_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
