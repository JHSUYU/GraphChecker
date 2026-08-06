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
        // Both calls return an interned String.  Their symbolic provenance
        // must travel on the returned operand edge without changing the
        // shared object's identity or symbolizing unrelated literal aliases.
        String booleanStatic = Boolean.toString(booleanValue.booleanValue());
        String booleanInstance = booleanValue.toString();
        String booleanPeer = "true";
        require(booleanStatic == booleanPeer && booleanInstance == booleanPeer,
                "Boolean conversion did not preserve interned identity");

        // Consume both returned edges in real predicates.  Merely computing
        // the conversions above is not a path decision; these contains calls
        // are what make the unsupported conversion provenance reportable.
        boolean booleanStaticMatches = booleanStatic.contains("true");
        System.markConcolicBranch("STRING.CONVERSION.BOOLEAN.STATIC", 1);
        if (!booleanStaticMatches) {
            throw new AssertionError("unexpected static Boolean text");
        }
        boolean booleanInstanceMatches = booleanInstance.contains("true");
        System.markConcolicBranch("STRING.CONVERSION.BOOLEAN.INSTANCE", 1);
        if (!booleanInstanceMatches) {
            throw new AssertionError("unexpected instance Boolean text");
        }

        // A separate alias of the same interned oop remains concrete.
        boolean peerMatches = booleanPeer.contains("true");
        System.markConcolicBranch("STRING.CONVERSION.BOOLEAN.PEER", 1);
        if (!peerMatches) {
            throw new AssertionError("unexpected peer Boolean text");
        }

        StringBuilder builder = new StringBuilder();
        builder.append("key=").append(integer.intValue());
        // The previous append makes the builder symbolic.  A later append
        // executes concrete AbstractStringBuilder.value/count writes while
        // preserving the builder's reference-level concat model.
        builder.append("!");
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
        String branchEvents = System.getConcolicBranchEvents();
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
        require(oneCondition(branchEvents,
                "STRING.CONVERSION.BOOLEAN.STATIC"), branchEvents);
        require(oneCondition(branchEvents,
                "STRING.CONVERSION.BOOLEAN.INSTANCE"), branchEvents);
        require(emptyCondition(branchEvents,
                "STRING.CONVERSION.BOOLEAN.PEER"), branchEvents);
        // getSymbolicExpression is observational and must not add an otherwise
        // unused value to the path condition.
        require(summary.contains("\"regionId\":\"REGION.string-conversion\""),
                summary);
        require(summary.contains(
                "\"taskId\":\"ACT.string-conversion\""), summary);
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

    private static boolean oneCondition(String events, String site) {
        String event = event(events, site);
        return event.contains("\"conditionCount\":1")
                && !event.contains("\"conditionIndices\":[]");
    }

    private static boolean emptyCondition(String events, String site) {
        String event = event(events, site);
        return event.contains("\"conditionCount\":0")
                && event.contains("\"conditionIndices\":[]");
    }

    private static String event(String events, String site) {
        String identity = "\"siteId\":\"" + site + "\"";
        int identityOffset = events.indexOf(identity);
        if (identityOffset < 0) return "";
        int start = events.lastIndexOf('{', identityOffset);
        int end = events.indexOf('}', identityOffset);
        return start < 0 || end < start ? "" : events.substring(start,
                end + 1);
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
