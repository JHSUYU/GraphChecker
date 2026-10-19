package edu.uva.liftlab.graphchecker.smt;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

public final class VmRows {
    private VmRows() {
    }

    public static final String GUARDED_READ_TYPE = "ReadFromExpression";
    public static final String OBSERVED_VERSION = "observedVersion";
    public static final String WRITER_SET_COMPLETE = "writerSetComplete";
    public static final String OBSERVED_EXACT = "observedExact";
    public static final String UNNAMED_WRITER = "unnamedWriter";

    public static boolean joinable(JsonObject read) {
        return writerSetComplete(read) || flag(read, OBSERVED_EXACT, false);
    }

    public static long readEvent(JsonObject read) {
        if (read == null) return -1L;
        long event = optionalLongInteger(read, "readEventId", -1L);
        return event >= 0L ? event
                : optionalLongInteger(read, "eventId", -1L);
    }

    public static long recordedVersion(JsonObject read) {
        JsonElement observed = read == null ? null
                : read.get(OBSERVED_VERSION);
        if (observed == null || !observed.isJsonObject()) return -1L;
        JsonElement id = observed.getAsJsonObject().get("fieldVersionId");
        return id == null || !id.isJsonPrimitive() ? -1L : id.getAsLong();
    }

    public static long joinedVersion(JsonObject read) {
        return joinable(read) ? recordedVersion(read) : -1L;
    }

    private static boolean writerSetComplete(JsonObject read) {
        return flag(read, WRITER_SET_COMPLETE, true);
    }

    public static boolean unnamedWriter(JsonObject read) {
        return flag(read, UNNAMED_WRITER, false);
    }

    private static boolean flag(JsonObject read, String member,
                                boolean absent) {
        JsonElement value = read == null ? null : read.get(member);
        return value == null || !value.isJsonPrimitive() ? absent
                : value.getAsBoolean();
    }
    public static final String RECORDED_READING = "inSessionRecordedReading";
    public static final String CONTAINER_BASE_UNSTATED =
            "CONTAINER_BASE_UNSTATED";

    private static final Pattern ARRAY_IDENTITY =
            Pattern.compile("A[A-Z\\[]_(\\d+)-\\d+");
    private static final String TRUNCATED_EXPRESSION_TYPE =
            "TruncatedExpression";
    private static final String TRUNCATION_AUTHORITY =
            "VM_SERIALIZATION_TRUNCATION_V1";

    public static boolean placedObject(String symbol) {
        return symbol != null && symbol.startsWith("P_L'")
                && symbol.endsWith("'_");
    }

    public static String objectIdentity(String symbol) {
        if (symbol == null) return "";
        Matcher array = ARRAY_IDENTITY.matcher(symbol);
        return array.matches()
                ? symbol.substring(0, symbol.lastIndexOf('-')) : symbol;
    }

    private static final Pattern INSTANCE_IDENTITY =
            Pattern.compile("(M_L'[^']*'_)(\\d+)");

    public static String[] objectHandle(String value) {
        if (value == null) return null;
        Matcher instance = INSTANCE_IDENTITY.matcher(value);
        if (instance.matches()) {
            return new String[] {instance.group(1), instance.group(2)};
        }
        Matcher array = ARRAY_IDENTITY.matcher(value);
        return array.matches() ? new String[] {
                value.substring(0, array.start(1)), array.group(1)} : null;
    }

    public static long referencedObjectRid(String symbol) {
        if (symbol == null) return -1L;
        Matcher array = ARRAY_IDENTITY.matcher(symbol);
        if (array.matches()) return Long.parseLong(array.group(1));
        int quoted = symbol.lastIndexOf("'_");
        if (!symbol.startsWith("M_L'") || quoted < 0) return -1L;
        String digits = symbol.substring(quoted + 2);
        if (digits.isEmpty()) return -1L;
        for (int index = 0; index < digits.length(); index++) {
            if (!Character.isDigit(digits.charAt(index))) return -1L;
        }
        try {
            return Long.parseLong(digits);
        } catch (NumberFormatException notAnObject) {
            return -1L;
        }
    }

    public static boolean truncated(JsonElement expression) {
        for (ExpressionWalk walk = ExpressionWalk.of(expression);
             walk.hasNext(); ) {
            JsonObject term = walk.next();
            if (TRUNCATED_EXPRESSION_TYPE.equals(
                    optionalString(term, "_type"))
                    && TRUNCATION_AUTHORITY.equals(
                    optionalString(term, "expressionAuthority"))) {
                return true;
            }
        }
        return false;
    }
}
