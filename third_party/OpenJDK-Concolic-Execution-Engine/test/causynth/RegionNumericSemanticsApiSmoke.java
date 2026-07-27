public final class RegionNumericSemanticsApiSmoke {
    private static final class Input {
        int intValue = 65;
        long longValue = 4_294_967_361L;
        float floatValue = 3.5F;
        double doubleValue = 7.25D;
    }

    private static final class Capture {
        final String before;
        final String after;
        final String summary;
        final boolean outcome;

        Capture(String before, String after, String summary,
                boolean outcome) {
            this.before = before;
            this.after = after;
            this.summary = summary;
            this.outcome = outcome;
        }
    }

    private RegionNumericSemanticsApiSmoke() {
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }

    private static void requireCast(String expression, String source,
                                    String target) {
        require(expression.contains("\"_type\":\"TypeCastExpression\"")
                        && expression.contains("\"sourceJavaType\":\""
                        + source + "\"")
                        && expression.contains("\"targetJavaType\":\""
                        + target + "\"")
                        && expression.contains("\"_java_type\":\""
                        + target + "\""),
                "missing exact " + source + "->" + target
                        + " cast: " + expression);
    }

    private static void symbolize(Input input, String prefix) {
        System.symbolizeField(input, "intValue", prefix + "_int");
        System.symbolizeField(input, "longValue", prefix + "_long");
        System.symbolizeField(input, "floatValue", prefix + "_float");
        System.symbolizeField(input, "doubleValue", prefix + "_double");
    }

    private static void conversionSmoke() {
        Input input = new Input();
        long status = System.startConcolicRegion(
                "REGION.NUMERIC.CAST", "ACT.NUMERIC.CAST");
        require(status == 0L, "cast region start rejected");
        symbolize(input, "numeric_cast");
        String pathBeforeCasts = System.getPathCondition();

        float i2f = (float) input.intValue;
        long i2l = (long) input.intValue;
        double i2d = (double) input.intValue;
        int l2i = (int) input.longValue;
        float l2f = (float) input.longValue;
        double l2d = (double) input.longValue;
        int f2i = (int) input.floatValue;
        long f2l = (long) input.floatValue;
        double f2d = (double) input.floatValue;
        int d2i = (int) input.doubleValue;
        float d2f = (float) input.doubleValue;
        long d2l = (long) input.doubleValue;
        byte i2b = (byte) input.intValue;
        char i2c = (char) input.intValue;
        short i2s = (short) input.intValue;

        // Value conversions must not be inserted as assumptions.  This also
        // catches the historical old==cast(old) path-condition encoding.
        String pathAfterCasts = System.getPathCondition();
        // Box while propagation is enabled so each constructor consumes and
        // transfers the cast-local shadow.  Pause only the diagnostic native
        // calls below; pausing around construction would deliberately discard
        // the very value edges this smoke is meant to inspect.
        Float i2fBox = new Float(i2f);
        Long i2lBox = new Long(i2l);
        Double i2dBox = new Double(i2d);
        Integer l2iBox = new Integer(l2i);
        Float l2fBox = new Float(l2f);
        Double l2dBox = new Double(l2d);
        Integer f2iBox = new Integer(f2i);
        Long f2lBox = new Long(f2l);
        Double f2dBox = new Double(f2d);
        Integer d2iBox = new Integer(d2i);
        Float d2fBox = new Float(d2f);
        Long d2lBox = new Long(d2l);
        Byte i2bBox = new Byte(i2b);
        Character i2cBox = new Character(i2c);
        Short i2sBox = new Short(i2s);
        System.pauseConcolicPathCondition();
        String i2fExpression = System.getSymbolicExpression(i2fBox);
        String i2lExpression = System.getSymbolicExpression(i2lBox);
        String i2dExpression = System.getSymbolicExpression(i2dBox);
        String l2iExpression = System.getSymbolicExpression(l2iBox);
        String l2fExpression = System.getSymbolicExpression(l2fBox);
        String l2dExpression = System.getSymbolicExpression(l2dBox);
        String f2iExpression = System.getSymbolicExpression(f2iBox);
        String f2lExpression = System.getSymbolicExpression(f2lBox);
        String f2dExpression = System.getSymbolicExpression(f2dBox);
        String d2iExpression = System.getSymbolicExpression(d2iBox);
        String d2fExpression = System.getSymbolicExpression(d2fBox);
        String d2lExpression = System.getSymbolicExpression(d2lBox);
        String i2bExpression = System.getSymbolicExpression(i2bBox);
        String i2cExpression = System.getSymbolicExpression(i2cBox);
        String i2sExpression = System.getSymbolicExpression(i2sBox);
        System.resumeConcolicPathCondition();
        String summary = System.finishConcolicRegion();

        require(pathBeforeCasts.equals(pathAfterCasts),
                "casts polluted the path condition: " + pathAfterCasts);
        requireCast(i2fExpression, "I", "F");
        requireCast(i2lExpression, "I", "J");
        requireCast(i2dExpression, "I", "D");
        requireCast(l2iExpression, "J", "I");
        requireCast(l2fExpression, "J", "F");
        requireCast(l2dExpression, "J", "D");
        requireCast(f2iExpression, "F", "I");
        requireCast(f2lExpression, "F", "J");
        requireCast(f2dExpression, "F", "D");
        requireCast(d2iExpression, "D", "I");
        requireCast(d2fExpression, "D", "F");
        requireCast(d2lExpression, "D", "J");
        requireCast(i2bExpression, "I", "B");
        requireCast(i2cExpression, "I", "C");
        requireCast(i2sExpression, "I", "S");
        require(!summary.contains("\"_type\":\"TypeCastExpression\""),
                summary);
    }

    private static Capture captureLongComparison() {
        Input input = new Input();
        long status = System.startConcolicRegion(
                "REGION.NUMERIC.LCMP", "ACT.NUMERIC.LCMP");
        require(status == 0L, "lcmp region start rejected");
        System.symbolizeField(input, "longValue", "numeric_lcmp_long");
        String before = System.getPathCondition();
        boolean outcome = input.longValue >= 0L;
        String after = System.getPathCondition();
        String summary = System.finishConcolicRegion();
        return new Capture(before, after, summary, outcome);
    }

    private static Capture captureDoubleNaN(boolean lessThan) {
        Input input = new Input();
        long status = System.startConcolicRegion(
                lessThan ? "REGION.NUMERIC.DCMPG" : "REGION.NUMERIC.DCMPL",
                lessThan ? "ACT.NUMERIC.DCMPG" : "ACT.NUMERIC.DCMPL");
        require(status == 0L, "double compare region start rejected");
        System.symbolizeField(input, "doubleValue", "numeric_double_nan");
        String before = System.getPathCondition();
        boolean outcome = lessThan
                ? input.doubleValue < Double.NaN
                : input.doubleValue > Double.NaN;
        String after = System.getPathCondition();
        String summary = System.finishConcolicRegion();
        return new Capture(before, after, summary, outcome);
    }

    private static Capture captureFloatNaN(boolean lessThan) {
        Input input = new Input();
        long status = System.startConcolicRegion(
                lessThan ? "REGION.NUMERIC.FCMPG" : "REGION.NUMERIC.FCMPL",
                lessThan ? "ACT.NUMERIC.FCMPG" : "ACT.NUMERIC.FCMPL");
        require(status == 0L, "float compare region start rejected");
        System.symbolizeField(input, "floatValue", "numeric_float_nan");
        String before = System.getPathCondition();
        boolean outcome = lessThan
                ? input.floatValue < Float.NaN
                : input.floatValue > Float.NaN;
        String after = System.getPathCondition();
        String summary = System.finishConcolicRegion();
        return new Capture(before, after, summary, outcome);
    }

    private static void requireComparison(Capture capture, String operator,
                                          String label) {
        require(!capture.before.contains("\"_op\":\"" + operator + "\""),
                label + " compare recorded a premature PC: "
                        + capture.before);
        require(!capture.outcome, label + " NaN outcome must be false");
        require(capture.after.contains("\"_op\":\"" + operator + "\"")
                        && capture.summary.contains(
                        "\"_op\":\"" + operator + "\""),
                label + " trichotomy was not retained: " + capture.after);
        require(capture.after.contains("\"_java_type\":\"I\"")
                        && capture.after.contains("Y_I_0"),
                label + " result was not compared as a JVM int: "
                        + capture.after);
    }

    public static void main(String[] args) {
        conversionSmoke();

        Capture lcmp = captureLongComparison();
        require(!lcmp.before.contains("\"_op\":\"--\""),
                "lcmp recorded before the consuming branch: " + lcmp.before);
        require(lcmp.outcome, "unexpected concrete lcmp outcome");
        require(lcmp.after.contains("\"_op\":\"--\"")
                        && lcmp.after.contains("Y_I_0"),
                "lcmp trichotomy did not reach the branch: " + lcmp.after);

        requireComparison(captureDoubleNaN(true), "--g", "dcmpless");
        requireComparison(captureDoubleNaN(false), "--l", "dcmpgreater");
        requireComparison(captureFloatNaN(true), "--g", "fcmpless");
        requireComparison(captureFloatNaN(false), "--l", "fcmpgreater");
        System.out.println("CAUSYNTH_REGION_NUMERIC_SEMANTICS_SMOKE_OK");
    }
}
